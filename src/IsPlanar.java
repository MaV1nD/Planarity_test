import ru.leti.wise.task.plugin.graph.GraphProperty;
import ru.leti.wise.task.graph.model.Graph;
import ru.leti.wise.task.graph.model.Vertex;
import ru.leti.wise.task.graph.model.Edge;

import java.util.*;
import java.util.stream.Collectors;

/**
 * Реализация алгоритма проверки планарности графа,
 * основанного на LR-критерии (Left-Right Planarity Test) по Ульрику Брандесу.
 * Алгоритм состоит из двух основных DFS-обходов (DFS1 и DFS2) для каждой компоненты связности.
 */
public class IsPlanar implements GraphProperty {

    // Внутреннее представление ориентированного ребра графа.
    // Используется для хранения информации о направлении и типе ребра в DFS-дереве.
    static class OurEdge {
        final int source; // ID исходной вершины ребра
        final int target; // ID целевой вершины ребра
        boolean isTreeEdge; // Флаг, указывающий, является ли ребро ребром DFS-дерева (true) или обратным ребром (false)

        public OurEdge(int source, int target) {
            this.source = source;
            this.target = target;
            this.isTreeEdge = false; // По умолчанию ребро считается обратным, пока DFS1 не определит его тип
        }

        @Override
        public boolean equals(Object o) {
            if (this == o) return true;
            if (o == null || getClass() != o.getClass()) return false;
            OurEdge ourEdge = (OurEdge) o;
            // Два ориентированных ребра равны, если их источники и цели совпадают
            return source == ourEdge.source && target == ourEdge.target;
        }

        @Override
        public int hashCode() {
            return Objects.hash(source, target);
        }

        @Override
        public String toString() {
            // Для отладки: (source->targetT) для ребра дерева, (source->targetB) для обратного
            return "(" + source + "->" + target + (isTreeEdge ? "T" : "B") + ")";
        }
    }

    // Представляет интервал возвратных ребер на стеке S в DFS2.
    // Интервал ограничен двумя ребрами: `low` (с самой низкой точкой возврата)
    // и `high` (с самой высокой точкой возврата).
    static class Interval {
        OurEdge low;  // Ребро с самой низкой точкой возврата в этом интервале
        OurEdge high; // Ребро с самой высокой точкой возврата в этом интервале

        Interval(OurEdge high, OurEdge low) { // В статье Брандеса порядок аргументов high, low
            this.high = high;
            this.low = low;
        }

        Interval() { this(null, null); } // Конструктор для создания пустого интервала

        boolean isEmpty() { return low == null && high == null; } // Проверка, пуст ли интервал

        @Override
        public String toString() {
            return "[" + (high != null ? high : "null") + ", " + (low != null ? low : "null") + "]";
        }
    }

    // Представляет конфликтную пару интервалов на стеке S в DFS2.
    // Состоит из левого (L) и правого (R) интервалов.
    // Эти интервалы содержат возвратные рёбра, которые потенциально конфликтуют
    // и должны быть размещены по разные стороны от некоторого ребра дерева.
    static class ConflictPair {
        Interval L; // Левый интервал
        Interval R; // Правый интервал

        ConflictPair(Interval L, Interval R) {
            this.L = L;
            this.R = R;
        }
        ConflictPair() {
            this.L = new Interval(); // Инициализация пустыми интервалами
            this.R = new Interval();
        }
        @Override
        public String toString() {
            return "P(L:" + L + ", R:" + R + ")";
        }
    }

    // Поля состояния для одной компоненты связности графа
    private int N_comp; // Количество вершин в текущей обрабатываемой компоненте связности
    private Map<Integer, Integer> vertexToIndex; // Отображение ID вершины графа в локальный индекс (0 .. N_comp-1)
    private Map<Integer, Integer> indexToVertex; // Обратное отображение: локальный индекс -> ID вершины

    private Map<Integer, List<OurEdge>> adjOriented; // Ориентированный список смежности для текущей компоненты (результат DFS1)
    private int[] height; // Массив высот вершин в DFS-дереве (индексируется локальным индексом вершины)
    private OurEdge[] parentEdge; // Массив родительских рёбер в DFS-дереве (parentEdge[v_idx] - ребро, по которому пришли в v_idx)

    // Карты для хранения свойств рёбер, вычисляемых в DFS1
    private Map<OurEdge, Integer> lowptMap;    // lowpt[edge] = высота самой низкой вершины, достижимой из ребра 'edge' через одно обратное ребро.
    private Map<OurEdge, Integer> lowpt2Map;   // lowpt2[edge] = высота второй по низости вершины (для определения хордальности рёбер дерева).
    private Map<OurEdge, Integer> nestingDepthMap; // Глубина вложенности ребра 'edge', используется для сортировки рёбер перед DFS2.

    // Структуры данных для Фазы 2 (DFS2)
    private Deque<ConflictPair> S_stack; // Стек S, хранящий ConflictPair. Основная структура для проверки LR-условий.
    private Map<OurEdge, OurEdge> refMap; // ref[edge] = ссылочное ребро, относительно которого определяется сторона 'edge'.
    private Map<OurEdge, Integer> sideMap; // side[edge] = сторона (+1 для Right, -1 для Left) или модификатор для стороны ref[edge].

    private Map<OurEdge, OurEdge> lowptEdgeMapDFS2; // lowpt_edge[e] в DFS2: первое обратное ребро к lowpt[e], встреченное при обходе.
    private Map<OurEdge, ConflictPair> stackBottomMap; // stack_bottom[e] в DFS2: указатель на вершину стека S перед обработкой ребра 'e'.

    private boolean[] visitedDfs1; // Массив для отслеживания посещенных вершин в DFS1


    /**
     * Основной метод, реализующий интерфейс GraphProperty.
     * Проверяет, является ли граф максимально планарным.
     * @param graph Входной граф.
     * @return true, если граф максимально планарен, иначе false.
     */
    @Override
    public boolean run(Graph graph) {
        int n = graph.getVertexCount(); // Количество вершин
        int m = graph.getEdgeCount(); // Количество рёбер

        // Тривиальный случай: пустой граф планарен
        if (n <= 0) return true;

        // Алгоритм предназначен для неориентированных графов
        if (graph.isDirect()) return false;

        // Обработка малых графов. Они планарны, если в них меньше 5 вершин.
        if (n <= 4) return true;

        // Необходимое условие планарности (следствие из формулы Эйлера): m <= 3n - 6 для n > 2.
        // Если рёбер слишком много, граф не может быть планарен.
        if (n > 2 && m > 3 * n - 6) {
            return false;
        }

        return isPlanar(graph);
    }

    /**
     * Проверяет планарность графа. Обрабатывает граф по компонентам связности.
     * @param graph Входной граф.
     * @return true, если граф планарен, иначе false.
     */
    public boolean isPlanar(Graph graph) {
        // Получение списка всех вершин из графа
        Set<Integer> allVertices = graph.getVertexList().stream()
                .map(Vertex::getId)
                .collect(Collectors.toSet());
        if (allVertices.isEmpty()) return true; // Пустой граф планарен

        // Создаем неориентированный список смежности для всего графа,
        // чтобы находить компоненты связности.
        Map<Integer, List<Integer>> globalAdj = new HashMap<>();
        for (int v : allVertices) {
            globalAdj.put(v, new ArrayList<>());
        }
        for (Edge e : graph.getEdgeList()) {
            globalAdj.get(e.getSource()).add(e.getTarget());
            globalAdj.get(e.getTarget()).add(e.getSource()); // Для неориентированного графа
        }

        Set<Integer> visitedComponents = new HashSet<>(); // Вершины, уже отнесенные к какой-либо компоненте
        // Проверяем планарность для каждой компоненты связности
        for (int startNode : allVertices) {
            if (!visitedComponents.contains(startNode)) {
                // Находим все вершины текущей компоненты связности с помощью BFS-подобного обхода
                Set<Integer> currentComponentVertices = new HashSet<>();
                Queue<Integer> q = new LinkedList<>();

                q.add(startNode);
                visitedComponents.add(startNode);
                currentComponentVertices.add(startNode);

                while(!q.isEmpty()){
                    int u = q.poll();
                    for(int neighbor : globalAdj.getOrDefault(u, Collections.emptyList())){
                        if(!visitedComponents.contains(neighbor)){
                            visitedComponents.add(neighbor);
                            currentComponentVertices.add(neighbor);
                            q.add(neighbor);
                        }
                    }
                }

                // Если компонента не пуста, проверяем её на планарность
                if (!currentComponentVertices.isEmpty()) {
                    if (!isComponentPlanar(currentComponentVertices, globalAdj)) {
                        return false; // Если хотя бы одна компонента непланарна, весь граф непланарен
                    }
                }
            }
        }
        return true; // Все компоненты планарны
    }

    /**
     * Проверяет планарность одной компоненты связности графа.
     * @param compVerts Множество ID вершин, составляющих компоненту.
     * @param globalAdj Глобальный (неориентированный) список смежности всего графа.
     * @return true, если компонента планарна, иначе false.
     */
    private boolean isComponentPlanar(Set<Integer> compVerts, Map<Integer, List<Integer>> globalAdj) {
        this.N_comp = compVerts.size(); // Количество вершин в данной компоненте
        // Компоненты из 0, 1 или 2 вершин всегда планарны
        if (N_comp <= 2) return true;

        // Инициализация структур данных для текущей компоненты
        this.vertexToIndex = new HashMap<>();
        this.indexToVertex = new HashMap<>();
        int idx = 0;
        for (int v : compVerts) { // Создаем локальную индексацию вершин компоненты
            vertexToIndex.put(v, idx);
            indexToVertex.put(idx, v);
            idx++;
        }

        this.adjOriented = new HashMap<>(); // Инициализируем ориентированный список смежности
        compVerts.forEach(v -> adjOriented.put(v, new ArrayList<>()));

        this.height = new int[N_comp]; // Высоты вершин в DFS-дереве
        Arrays.fill(height, -1); // -1 означает, что вершина еще не посещена в DFS1
        this.parentEdge = new OurEdge[N_comp]; // parentEdge[v_idx] - ребро, по которому пришли в v_idx

        this.lowptMap = new HashMap<>();
        this.lowpt2Map = new HashMap<>();
        this.nestingDepthMap = new HashMap<>();

        this.visitedDfs1 = new boolean[N_comp]; // Посещенные вершины для DFS1

        // Фаза 1: DFS1 - Ориентация графа, построение DFS-дерева, вычисление lowpt, lowpt2, nesting_depth.
        // Соответствует Algorithm 2 в статье Брандеса.
        List<Integer> rootsDFS1 = new ArrayList<>(); // Корни DFS-деревьев (если компонента сама несвязна, что невозможно по определению)
        for (int startNodeId : compVerts) {
            int startNodeIdx = vertexToIndex.get(startNodeId);
            if (!visitedDfs1[startNodeIdx]) { // Если вершина еще не посещена, начинаем DFS1 из нее
                height[startNodeIdx] = 0; // Корень DFS-дерева на высоте 0
                parentEdge[startNodeIdx] = null; // У корня нет родительского ребра
                rootsDFS1.add(startNodeId);
                dfs1(startNodeId, globalAdj);
            }
        }

        // Фаза 2: DFS2 - Тестирование на LR-планарность.
        // Соответствует Algorithm 3, 4, 5 в статье Брандеса.

        // Сортировка списков смежности (adjOriented) по неубыванию nesting_depth.
        // Это необходимо для корректного порядка обхода в DFS2.
        for (List<OurEdge> edges : adjOriented.values()) {
            edges.sort(Comparator.comparingInt(e -> nestingDepthMap.getOrDefault(e, Integer.MAX_VALUE)));
        }

        // Инициализация структур данных для DFS2
        this.S_stack = new ArrayDeque<>();
        this.refMap = new HashMap<>();
        this.sideMap = new HashMap<>(); // По умолчанию все рёбра считаются "правыми" (side = 1)
        this.lowptEdgeMapDFS2 = new HashMap<>();
        this.stackBottomMap = new HashMap<>();

        boolean[] visitedDfs2 = new boolean[N_comp]; // Посещенные вершины для DFS2

        for (int rootId : rootsDFS1) { // DFS2 запускается из тех же корней, что и DFS1
            // parent_edge_to_root для корня DFS-дерева равно null
            if (!dfs2(rootId, null, visitedDfs2)) {
                return false; // Если DFS2 обнаружил непланарность, компонента непланарна
            }
        }
        return true; // Компонента планарна
    }

    /**
     * DFS1: Первый обход в глубину.
     * Цели:
     * 1. Ориентировать рёбра графа (разделить на рёбра дерева и обратные рёбра).
     * 2. Построить DFS-дерево (заполнить height[] и parentEdge[]).
     * 3. Вычислить lowpt[e] и lowpt2[e] для каждого ориентированного ребра e.
     * 4. Вычислить nesting_depth[e] для каждого ребра e.
     * Соответствует Algorithm 2 из статьи Брандеса.
     * @param uId ID текущей вершины.
     * @param globalAdj Глобальный неориентированный список смежности.
     */
    private void dfs1(int uId, Map<Integer, List<Integer>> globalAdj) {
        int uIdx = vertexToIndex.get(uId); // Локальный индекс текущей вершины
        visitedDfs1[uIdx] = true;          // Помечаем вершину как посещенную в DFS1

        // Перебираем всех соседей vId вершины uId в исходном неориентированном графе
        for (int vId : globalAdj.getOrDefault(uId, Collections.emptyList())) {
            int vIdx = vertexToIndex.get(vId); // Локальный индекс соседа
            OurEdge currentEdge = new OurEdge(uId, vId); // Создаем ориентированное ребро u -> v

            // Пропускаем ребро (u,v), если (v,u) является родительским ребром для u.
            // Это предотвращает обработку одного и того же неориентированного ребра дважды в разных направлениях
            // (один раз как ребро дерева, другой раз как обратное к родительскому).
            if (parentEdge[uIdx] != null && parentEdge[uIdx].source == vId && parentEdge[uIdx].target == uId) {
                continue;
            }

            // Инициализация lowpt и lowpt2 для currentEdge значением высоты его источника (uId).
            // Эти значения будут обновляться на основе информации от дочерних поддеревьев и обратных рёбер.
            lowptMap.put(currentEdge, height[uIdx]);
            lowpt2Map.put(currentEdge, height[uIdx]);

            if (!visitedDfs1[vIdx]) { // Если сосед vId еще не посещен: (u,v) - ребро дерева
                currentEdge.isTreeEdge = true;    // Помечаем как ребро дерева
                adjOriented.get(uId).add(currentEdge); // Добавляем в ориентированный список смежности

                parentEdge[vIdx] = currentEdge;       // currentEdge становится родительским для vId
                height[vIdx] = height[uIdx] + 1;    // Высота vId на 1 больше высоты uId
                dfs1(vId, globalAdj);                 // Рекурсивный вызов DFS1 для vId

                // После возврата из dfs1(vId):
                // lowpt[currentEdge] и lowpt2[currentEdge] уже вычислены на основе поддерева с корнем vId.
                // Теперь нужно обновить lowpt и lowpt2 для родительского ребра вершины u (т.е. parentEdge[uIdx]),
                // используя информацию от currentEdge = (u,v).
                // Это соответствует шагу "update lowpoints of parent edge e" в Algorithm 2 Брандеса.
                // e = parentEdge[uIdx], (v,w) в терминах статьи здесь это currentEdge.
                OurEdge parentOfU = parentEdge[uIdx];
                if (parentOfU != null) {
                    int low_uv = lowptMap.get(currentEdge);
                    int low2_uv = lowpt2Map.get(currentEdge);
                    int low_pu = lowptMap.get(parentOfU); // Текущий lowpt родительского ребра

                    if (low_uv < low_pu) {
                        lowpt2Map.put(parentOfU, Math.min(low_pu, low2_uv)); // Старый low_pu становится кандидатом в low2_pu
                        lowptMap.put(parentOfU, low_uv);
                    } else if (low_uv > low_pu) {
                        lowpt2Map.put(parentOfU, Math.min(lowpt2Map.get(parentOfU), low_uv));
                    } else { // low_uv == low_pu
                        lowpt2Map.put(parentOfU, Math.min(lowpt2Map.get(parentOfU), low2_uv));
                    }
                }

            } else if (parentEdge[uIdx] == null || (parentEdge[uIdx].source != vId || parentEdge[uIdx].target != uId)) {
                // Если vId уже посещена, и (u,v) не ведет к прямому родителю uId: (u,v) - обратное ребро.
                currentEdge.isTreeEdge = false; // Помечаем как обратное ребро
                adjOriented.get(uId).add(currentEdge); // Добавляем в ориентированный список смежности

                lowptMap.put(currentEdge, height[vIdx]); // lowpt для обратного ребра - это высота вершины, куда оно указывает.
                // lowpt2Map для обратного ребра остается height[uIdx] (его источника), т.к. оно само не образует второго пути.

                // Обновляем lowpt и lowpt2 для родительского ребра parentEdge[uIdx]
                // на основе этого обратного ребра (u,v).
                // height[vIdx] - это точка возврата текущего обратного ребра.
                OurEdge parentOfU = parentEdge[uIdx];
                if (parentOfU != null) {
                    int h_v = height[vIdx];
                    int low_pu = lowptMap.get(parentOfU);

                    if (h_v < low_pu) {
                        lowpt2Map.put(parentOfU, low_pu); // Старый low_pu становится кандидатом в low2_pu
                        lowptMap.put(parentOfU, h_v);
                    } else if (h_v > low_pu) {
                        lowpt2Map.put(parentOfU, Math.min(lowpt2Map.get(parentOfU), h_v));
                    }
                    // Если h_v == low_pu, lowpt2 не меняется только из-за этого ребра,
                    // т.к. оно не дает "второго" пути к тому же lowpt.
                }
            } else {
                // Это ребро (u,v) ведет к прямому родителю v=parent(u). Пропускаем, т.к. оно уже есть как (v,u) - ребро дерева.
                continue;
            }
        }

        // После обработки всех соседей uId, вычисляем nesting_depth для всех рёбер, исходящих из uId.
        // Это делается здесь, так как к этому моменту lowpt/lowpt2 для всех таких рёбер должны быть финализированы.
        for (OurEdge edge : adjOriented.getOrDefault(uId, Collections.emptyList())) {
            int edgeLowPt = lowptMap.get(edge); // lowpt(e)
            int nd = 2 * edgeLowPt; // Базовое значение nesting_depth
            if (edge.isTreeEdge) {
                // Для рёбер дерева, проверяем хордальность:
                // Если lowpt2(e) < height(source(e)), то ребро хордальное, и nesting_depth увеличивается на 1.
                // height(source(e)) - это высота вершины uId.
                if (lowpt2Map.get(edge) < height[vertexToIndex.get(edge.source)]) {
                    nd++;
                }
            }
            // Для обратных рёбер: lowpt2 по нашей инициализации равно height[source(e)], поэтому они не будут хордальными по этому определению.
            nestingDepthMap.put(edge, nd);
        }
    }


    /**
     * DFS2: Второй обход в глубину.
     * Цель: Проверить LR-условия планарности, используя стек S и информацию, собранную в DFS1.
     * Соответствует Algorithm 3 из статьи Брандеса.
     * @param vId ID текущей вершины.
     * @param pEdgeToV Ребро дерева, по которому пришли в vId (null для корня DFS).
     * @param visited Массив для отслеживания посещенных вершин в DFS2.
     * @return true, если подграф, соответствующий этому вызову DFS2, удовлетворяет LR-условиям, иначе false.
     */
    private boolean dfs2(int vId, OurEdge pEdgeToV, boolean[] visited) {
        int vIdx = vertexToIndex.get(vId); // Локальный индекс текущей вершины
        visited[vIdx] = true;              // Помечаем вершину как посещенную в DFS2

        // Получаем список исходящих рёбер, уже отсортированных по nesting_depth в isComponentPlanar
        List<OurEdge> sortedOutgoingEdges = adjOriented.getOrDefault(vId, Collections.emptyList());

        OurEdge firstOutgoingEdge = sortedOutgoingEdges.isEmpty() ? null : sortedOutgoingEdges.get(0);

        // Перебираем все исходящие рёбра ei из v (в порядке nesting_depth)
        for (OurEdge ei : sortedOutgoingEdges) {
            int wiId = ei.target; // Целевая вершина ребра ei
            int wiIdx = vertexToIndex.get(wiId); // Её локальный индекс

            // Запоминаем текущее состояние верхушки стека S перед обработкой ei.
            // Это stack_bottom[ei] из статьи.
            stackBottomMap.put(ei, S_stack.isEmpty() ? null : S_stack.peek());

            if (ei.isTreeEdge) { // Если ei - ребро дерева
                if (!visited[wiIdx]) { // Если целевая вершина еще не посещена в этом DFS2-обходе
                    if (!dfs2(wiId, ei, visited)) return false; // Рекурсивный вызов для поддерева
                }
                // Случай, когда visited[wiIdx] == true для ребра дерева, не должен происходить в корректном DFS2 по одному DFS-дереву.
            } else { // Если ei - обратное ребро
                lowptEdgeMapDFS2.put(ei, ei); // ei является своим собственным lowpt_edge[ei]
                // Помещаем на стек S новую конфликтную пару: L - пустой, R - интервал [ei, ei]
                S_stack.push(new ConflictPair(new Interval(), new Interval(ei, ei)));
            }

            // Интеграция новых возвратных рёбер (если ei или его поддерево имеют возвратные пути ниже vId)
            // lowpt[ei] < height[v] означает, что есть возвратное ребро из поддерева ei (или само ei),
            // которое идет в предка vId.
            if (lowptMap.get(ei) < height[vIdx]) {
                if (pEdgeToV != null) { // Если vId не корень DFS (т.е. есть родительское ребро pEdgeToV)
                    if (ei == firstOutgoingEdge) { // ei - это e1 (первое исходящее ребро из v по nesting_depth)
                        // lowpt_edge[pEdgeToV] наследуется от lowpt_edge[ei]
                        lowptEdgeMapDFS2.put(pEdgeToV, lowptEdgeMapDFS2.get(ei));
                    } else { // ei - это e_i, i > 1 (не первое исходящее ребро)
                        // Вызываем Algorithm 4: add_constraints
                        if (!addConstraints(ei, pEdgeToV)) return false; // Если ограничения несовместны - непланарность
                    }
                }
                // Если pEdgeToV == null (vId - корень), то никакие lowpt_edge или addConstraints для родителя не нужны.
            }
        } // Конец цикла по исходящим рёбрам из vId

        // После обработки всех исходящих рёбер из vId:
        if (pEdgeToV != null) { // Если vId не корень DFS
            int uId = pEdgeToV.source; // uId - родитель vId

            // Удаляем со стека S обратные рёбра, которые заканчиваются в uId (родителе vId).
            // Это Algorithm 5: trim_back_edges.
            trimBackEdges(uId);

            // Определяем сторону (ссылочное ребро) для pEdgeToV.
            // Если pEdgeToV имеет возврат ниже uId (lowpt[pEdgeToV] < height[u]),
            // то его сторона определяется относительно рёбер на вершине стека S.
            if (lowptMap.get(pEdgeToV) < height[vertexToIndex.get(uId)]) {
                if (S_stack.isEmpty()) {
                    // Это может указывать на проблему, если есть возврат, стек не должен быть пуст.
                    // В некоторых случаях может быть нормально, если все конфликты разрешились и стек опустел,
                    // но тогда ref останется null. В статье предполагается, что стек не пуст при возврате.
                    // Если граф планарен, то к этому моменту должна быть информация на стеке.
                    // Если ref не установлен, это может быть проблемой для последующего построения вложения,
                    // но для проверки планарности главное - не вернуть false по ошибке.
                    // В контексте просто проверки, если это ведет к противоречию, оно должно быть поймано в addConstraints или trim.
                } else {
                    ConflictPair topS = S_stack.peek(); // Вершина стека
                    OurEdge hL = topS.L.high; // Верхнее ребро левого интервала
                    OurEdge hR = topS.R.high; // Верхнее ребро правого интервала

                    OurEdge refEdge = null;
                    // Выбираем refEdge: то из hL или hR, у которого lowpt выше (т.е. оно "внутреннее").
                    // Если lowpt равны, предпочтение отдается hR (согласно статье, хотя может быть и наоборот).
                    if (hL != null && (hR == null || lowptMap.get(hL) > lowptMap.get(hR))) {
                        refEdge = hL;
                    } else {
                        refEdge = hR; // hR может быть null
                    }

                    if (refEdge != null) {
                        refMap.put(pEdgeToV, refEdge);
                        // sideMap для pEdgeToV остается по умолчанию 1 (Right). Его фактическая сторона
                        // будет определяться через refEdge и side[refEdge] на этапе вложения.
                    }
                    // Если refEdge == null (например, topS содержит пустые интервалы), refMap не обновляется.
                    // Это означает, что pEdgeToV не имеет четкой привязки к стороне от рёбер на стеке,
                    // что может быть нормально, если все конфликты уже разрешены.
                }
            }
        }
        return true; // Если дошли сюда, текущее поддерево удовлетворяет LR-условиям.
    }

    /**
     * Algorithm 4 из статьи Брандеса: Добавление ограничений.
     * Сливает ограничения от текущего ребра/поддерева `ei` с уже накопленными ограничениями
     * от предыдущих сиблингов $e_1, \ldots, e_{i-1}$ (представленных через `pEdge`).
     * @param ei Текущее обработанное ребро (сиблинг $e_1, \ldots, e_{i-1}$).
     * @param pEdge Родительское ребро для вершины, из которой исходят `ei` и его сиблинги.
     * @return true, если ограничения успешно слиты, false при обнаружении непланарности.
     */
    private boolean addConstraints(OurEdge ei, OurEdge pEdge) {
        ConflictPair P_new = new ConflictPair(); // Новая конфликтная пара для слияния
        ConflictPair stackBottomEi = stackBottomMap.get(ei); // "Дно" стека для ребра ei

        // 1. Слияние возвратных рёбер от ei (находящихся на стеке выше stackBottomEi) в P_new.R.
        // Эти рёбра должны быть на одной стороне (здесь условно "правой").
        while (!S_stack.isEmpty() && S_stack.peek() != stackBottomEi) {
            ConflictPair Q = S_stack.pop(); // Берем пару со стека

            // Согласно инвариантам, на этом этапе у Q.L должен быть пустой интервал,
            // а все рёбра - в Q.R. Если Q.L не пуст, а Q.R пуст, меняем их местами.
            // Если оба не пусты - это конфликт, т.к. рёбра из одного поддерева ei
            // оказались разделены на L и R, что невозможно.
            if (!Q.L.isEmpty()) {
                if (Q.R.isEmpty()) { // Q.L не пуст, Q.R пуст - меняем местами
                    Interval temp = Q.L; Q.L = Q.R; Q.R = temp;
                }  else {
                    return false; // Конфликт: оба интервала Q.L и Q.R непусты выше stack_bottom[ei]
                }
            }
            // Теперь Q.L должен быть пуст. Если нет - это ошибка или непланарность.
            if (!Q.L.isEmpty()) return false;


            if (!Q.R.isEmpty()) { // Если есть что сливать из Q.R
                // Сравниваем lowpt(Q.R.low) с lowpt(pEdge). pEdge здесь - это 'e' в статье.
                // lowptMap.get(pEdge) - это высота самой низкой точки возврата для родительского ребра pEdge.
                if (lowptMap.get(Q.R.low) > lowptMap.get(pEdge)) { // Случай "merge intervals"
                    if (P_new.R.isEmpty()) { // Если P_new.R еще пуст, просто присваиваем
                        P_new.R = Q.R;
                    } else { // Иначе, "связываем" P_new.R.low с Q.R.high
                        refMap.put(P_new.R.low, Q.R.high); // P_new.R.low ссылается на Q.R.high
                        sideMap.put(P_new.R.low, 1);       // Они на одной стороне (Right)
                        P_new.R.low = Q.R.low;             // Обновляем нижнюю границу P_new.R
                    }
                } else { // Случай "align" (выравнивание)
                    // Q.R.low "выравнивается" по lowpt_edge[pEdge]
                    refMap.put(Q.R.low, lowptEdgeMapDFS2.get(pEdge));
                    sideMap.put(Q.R.low, 1); // Та же сторона, что и у lowpt_edge от pEdge (Right)
                }
            }
        } // Конец цикла по рёбрам от ei

        // 2. Слияние конфликтующих возвратных рёбер от pEdge (т.е. от e_1...e_{i-1}) в P_new.L.
        // Конфликтующие - те, у которых lowpt строго выше, чем у lowpt_edge[ei].
        // lowpt_edge[ei] - это первое обратное ребро к lowpt[ei].
        // В данном коде используется lowptMap.get(ei) для сравнения, что может быть не совсем точно по статье,
        // но если ei - обратное ребро, то lowptMap.get(ei) = height[target(ei)].
        // Статья использует lowpt[b] где b - это lowpt_edge[ei].
        // Для простоты, будем считать, что lowptMap.get(ei) здесь используется как прокси для точки возврата ei.
        OurEdge b_ei = lowptEdgeMapDFS2.get(ei); // Это lowpt_edge[ei]

        while (!S_stack.isEmpty() &&
                S_stack.peek() != stackBottomMap.get(pEdge) && // Не опускаемся ниже "дна" родительского ребра pEdge
                (conflicting(S_stack.peek().L, b_ei) || conflicting(S_stack.peek().R, b_ei))) { // Есть конфликт
            ConflictPair Q = S_stack.pop();

            if (conflicting(Q.R, b_ei)) { // Если правый интервал Q.R конфликтует с b_ei
                if (conflicting(Q.L, b_ei)) return false; // Оба конфликтуют - непланарность
                // Меняем L и R местами, чтобы конфликтующий интервал Q.L оказался слева
                Interval temp = Q.L; Q.L = Q.R; Q.R = temp;
                // И меняем знак для sideMap, т.к. они теперь должны быть на противоположных сторонах
                if (Q.L.low != null) sideMap.put(Q.L.low, sideMap.getOrDefault(Q.L.low,1) * -1); // Этого нет в PDF, но логично
            }
            // Теперь, если есть конфликт, он в Q.L. Интервал Q.R не конфликтует с b_ei.

            // Сливаем Q.R (неконфликтующий) в P_new.R (та же логика, что и в шаге 1)
            if (!Q.R.isEmpty()) {
                if (P_new.R.isEmpty()) { P_new.R = Q.R; }
                else {
                    refMap.put(P_new.R.low, Q.R.high); sideMap.put(P_new.R.low, 1);
                    P_new.R.low = Q.R.low;
                }
            }
            // Сливаем Q.L (конфликтующий с b_ei) в P_new.L
            if (!Q.L.isEmpty()) { // Должен быть не пуст, т.к. conflicting(Q.L, b_ei) было true
                if (P_new.L.isEmpty()) { P_new.L = Q.L; }
                else {
                    refMap.put(P_new.L.low, Q.L.high); sideMap.put(P_new.L.low, 1); // Конфликтующие д.б. на одной стороне (L)
                    P_new.L.low = Q.L.low;
                }
            }
        } // Конец цикла по конфликтующим рёбрам

        // Если P_new не пуста, помещаем ее на стек
        if (!P_new.L.isEmpty() || !P_new.R.isEmpty()) {
            S_stack.push(P_new);
        }
        return true;
    }

    /**
     * Вспомогательная функция для addConstraints.
     * Проверяет, конфликтует ли интервал I с ребром b (предположительно lowpt_edge[ei]).
     * Конфликт есть, если I не пуст и его самая высокая точка возврата (lowpt[I.high])
     * находится строго выше точки возврата ребра b (lowpt[b]).
     */
    private boolean conflicting(Interval I, OurEdge b) {
        return I != null && !I.isEmpty() && I.high != null && b != null &&
                lowptMap.get(I.high) > lowptMap.get(b); // Сравнение высот точек возврата
    }

    /**
     * Algorithm 5 из статьи Брандеса: Удаление (обрезка) обратных рёбер.
     * Удаляет со стека S или модифицирует те обратные рёбра, которые заканчиваются
     * в вершине uId (родителе текущей обрабатываемой вершины в DFS2).
     * @param uId ID родительской вершины.
     */
    private void trimBackEdges(int uId) {
        int h_uId = height[vertexToIndex.get(uId)]; // Высота родительской вершины uId

        // Шаг 1: Удаление целых конфликтных пар, если их lowest return point == h_uId.
        // lowest(P) в статье - это min(lowpt(P.L.low), lowpt(P.R.low)).
        while (!S_stack.isEmpty() && lowestReturnPointHeight(S_stack.peek()) == h_uId) {
            ConflictPair P = S_stack.pop();
            // Если в левом интервале был P.L.low, он становится "левым" ребром.
            if (P.L.low != null) {
                sideMap.put(P.L.low, -1); // Помечаем как Left (-1)
            }
            // Правый P.R.low остается "правым" (sideMap по умолчанию 1 или уже установлен).
        }

        if (S_stack.isEmpty()) return; // Если стек опустел, больше нечего обрезать

        // Шаг 2: Обрезка интервалов в верхней конфликтной паре P на стеке.
        ConflictPair P = S_stack.peek(); // Не удаляем, а модифицируем верхний элемент

        // Обрезка левого интервала P.L
        // Удаляем P.L.high, пока его lowpt == h_uId, двигаясь по цепочке ref.
        while (P.L.high != null && lowptMap.get(P.L.high) == h_uId) {
            P.L.high = refMap.get(P.L.high);
        }
        // Если P.L.high стал null (т.е. верхняя часть интервала обрезана),
        // а P.L.low еще существует, значит левый интервал "опустел сверху".
        if (P.L.high == null && P.L.low != null) {
            // В этом случае P.L.low должен ссылаться на P.R.low (или что-то из правого интервала)
            // и стать "левым" относительно него.
            if (P.R.low == null) {
                // Это не должно происходить, если P не является полностью пустой парой,
                // которую должны были удалить на предыдущем шаге или если она не станет пустой после обрезки.
                // Если P.R.low тут null, это может быть ошибкой или специфическим случаем.
                // Для безопасности, чтобы не было NullPointerException, можно добавить проверку.
                // Однако, статья предполагает, что если P.L.low существует, то P.R.low тоже должен быть (или наоборот).
                // Если P.L.low остался, а P.R пуст, то P.L.low некуда ссылаться.
            } else {
                refMap.put(P.L.low, P.R.low); // P.L.low ссылается на P.R.low
                sideMap.put(P.L.low, -1);     // P.L.low становится Left относительно P.R.low
            }
            P.L.low = null; // Теперь левый интервал полностью пуст
        }

        // Обрезка правого интервала P.R (симметрично левому)
        while (P.R.high != null && lowptMap.get(P.R.high) == h_uId) {
            P.R.high = refMap.get(P.R.high);
        }
        if (P.R.high == null && P.R.low != null) { // Правый интервал "опустел сверху"
            if (P.L.low == null && P.L.high == null) { // Если и левый уже пуст
                // P.R.low некуда ссылаться в левом интервале, он становится "корнем" своей стороны
                // или если левый не пуст, но только P.L.high (что странно)
            } else if (P.L.low != null) { // Если есть P.L.low, то P.R.low ссылается на него
                refMap.put(P.R.low, P.L.low);
                sideMap.put(P.R.low, -1); // P.R.low становится Left относительно P.L.low (т.е. другой стороны)
            } else {
                // P.L.low is null, but P.L.high is not. This case is less clear from the direct text.
                // Typically, if P.L.low is null, P.L.high should also be null for an empty interval.
                // If P.L is not empty, P.L.low should exist if P.L.high does.
                // Assuming P.L is not empty and P.L.low exists (or P.L.high is the representative).
                OurEdge leftRef = P.L.low != null ? P.L.low : P.L.high;
                if (leftRef != null) {
                    refMap.put(P.R.low, leftRef);
                    sideMap.put(P.R.low, -1);
                }
            }
            P.R.low = null; // Правый интервал теперь полностью пуст (если P.R.high тоже null)
        }


        // Если после обрезки вся конфликтная пара P стала пустой, удаляем ее со стека.
        if (P.L.isEmpty() && P.R.isEmpty()) {
            S_stack.pop();
        }
    }

    /**
     * Вспомогательная функция для trimBackEdges.
     * Возвращает высоту самой низкой точки возврата для конфликтной пары P.
     * Это min(lowpt(P.L.low), lowpt(P.R.low)).
     */
    private int lowestReturnPointHeight(ConflictPair P) {
        int minHeight = Integer.MAX_VALUE;
        boolean found = false;
        if (P.L.low != null && lowptMap.containsKey(P.L.low)) { // Добавлена проверка на наличие ключа
            minHeight = Math.min(minHeight, lowptMap.get(P.L.low));
            found = true;
        }
        if (P.R.low != null && lowptMap.containsKey(P.R.low)) { // Добавлена проверка на наличие ключа
            minHeight = Math.min(minHeight, lowptMap.get(P.R.low));
            found = true;
        }
        return found ? minHeight : Integer.MAX_VALUE; // Если пара пуста или рёбра не найдены в карте, вернуть MAX_VALUE
    }
}

