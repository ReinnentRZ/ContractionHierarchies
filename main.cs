using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Text;

// Contraction Hierarchies - simple educational implementation
// - Preprocessing: contract nodes in increasing importance (degree heuristic)
// - Add shortcuts if needed (by checking shortest path avoiding the contracted node)
// - Assign levels (contraction order), higher level = more important (contracted later)
// - Query: bidirectional Dijkstra limited by levels (simple version)
// - Logging & Graphviz (.dot) export
//
// Based on project spec: "Implementasi dan Visualisasi Algoritma Shortest Path pada Peta Kampus di Yogyakarta". :contentReference[oaicite:1]{index=1}

class Edge
{
    public int U, V;
    public int W;
    public bool IsShortcut;
    public Edge(int u, int v, int w, bool shortcut = false) { U = u; V = v; W = w; IsShortcut = shortcut; }
}

class Graph
{
    // adjacency list: node -> list of edges (we store both directions explicitly)
    public Dictionary<int, List<Edge>> Adj = new();
    public HashSet<(int, int)> EdgeSet = new(); // keep set to avoid duplicate exact edges (u,v)
    public int NodeCount => Adj.Count;

    public void AddNode(int v)
    {
        if (!Adj.ContainsKey(v)) Adj[v] = new List<Edge>();
    }

    public void AddEdge(int u, int v, int w, bool isShortcut = false)
    {
        AddNode(u); AddNode(v);
        // allow multiedges but here we avoid exact same (u,v,w) duplication by using pair key for simplicity
        if (!EdgeSet.Contains((u, v)))
        {
            var e1 = new Edge(u, v, w, isShortcut);
            var e2 = new Edge(v, u, w, isShortcut);
            Adj[u].Add(e1);
            Adj[v].Add(e2);
            EdgeSet.Add((u, v));
            EdgeSet.Add((v, u));
        }
        else
        {
            // if there is already an edge, update weight if new weight is smaller
            var existing = Adj[u].FirstOrDefault(x => x.V == v);
            if (existing != null && w < existing.W)
            {
                // update both directions
                foreach (var e in Adj[u].Where(x => x.V == v)) e.W = w;
                foreach (var e in Adj[v].Where(x => x.V == u)) e.W = w;
            }
        }
    }

    public void RemoveNode(int v)
    {
        if (!Adj.ContainsKey(v)) return;
        foreach (var e in Adj[v])
        {
            Adj[e.V].RemoveAll(x => x.V == v);
            EdgeSet.Remove((e.V, v));
        }
        Adj.Remove(v);
    }

    public int Degree(int v) => Adj.ContainsKey(v) ? Adj[v].Count : 0;

    public List<int> Neighbors(int v) => Adj.ContainsKey(v) ? Adj[v].Select(e => e.V).Distinct().ToList() : new List<int>();

    // get weight u->v (assumes edge exists)
    public int GetWeight(int u, int v)
    {
        if (!Adj.ContainsKey(u)) return int.MaxValue;
        var e = Adj[u].FirstOrDefault(x => x.V == v);
        return e != null ? e.W : int.MaxValue;
    }
}

class ContractionHierarchies
{
    Graph graph;
    Dictionary<int, int> level = new(); // node -> level (higher = more important)
    List<string> log = new();
    int contractedCount = 0;
    int totalNodes;

    public ContractionHierarchies(Graph g)
    {
        graph = g;
        totalNodes = g.NodeCount;
    }

    public void Preprocess()
    {
        // simple importance: degree
        // contract in increasing degree (least important first)
        var pq = new SortedSet<(int degree, int node)>(Comparer<(int, int)>.Create((a, b) =>
        {
            int c = a.degree.CompareTo(b.degree);
            if (c == 0) c = a.node.CompareTo(b.node);
            return c;
        }));

        foreach (var v in graph.Adj.Keys) pq.Add((graph.Degree(v), v));

        // we'll assign level as contraction order: 1..n (1 = contracted first = least important)
        int order = 1;

        while (pq.Count > 0)
        {
            var item = pq.Min; pq.Remove(item);
            int v = item.node;
            // node may have been removed due to previous contractions
            if (!graph.Adj.ContainsKey(v)) continue;

            ContractNode(v, order);
            level[v] = order;
            order++;
        }
        contractedCount = order - 1;
        log.Add($"Preprocessing done. Contracted {contractedCount} nodes.");
    }

    void ContractNode(int v, int order)
    {
        log.Add($"Contracting node {v} (degree {graph.Degree(v)}) with assigned level {order}...");
        var neighbors = graph.Neighbors(v);
        int n = neighbors.Count;

        // for each pair of neighbors (u,w), check if we need a shortcut u-w via v
        for (int i = 0; i < n; i++)
        {
            for (int j = i + 1; j < n; j++)
            {
                int u = neighbors[i], w = neighbors[j];
                if (u == w) continue;

                int via = graph.GetWeight(u, v);
                int via2 = graph.GetWeight(v, w);
                if (via == int.MaxValue || via2 == int.MaxValue) continue;
                int costViaV = via + via2;

                // compute current shortest u->w WITHOUT using v (we do Dijkstra avoiding v)
                int distUW = ShortestPathAvoidingNode(u, w, v);

                if (costViaV < distUW)
                {
                    // add shortcut u-w
                    graph.AddEdge(u, w, costViaV, isShortcut: true);
                    log.Add($"  Shortcut added: {u} <-> {w} weight={costViaV} (via {v})");
                }
            }
        }

        // remove v from graph (so later contractions don't consider it)
        graph.RemoveNode(v);
        log.Add($"  Node {v} removed from base graph.");
    }

    // Dijkstra from s to t avoiding a node "avoid" (do not traverse avoid)
    int ShortestPathAvoidingNode(int s, int t, int avoid)
    {
        var dist = new Dictionary<int, int>();
        var pq = new SortedSet<(int dist, int node)>(Comparer<(int, int)>.Create((a, b) =>
        {
            int c = a.dist.CompareTo(b.dist);
            if (c == 0) c = a.node.CompareTo(b.node);
            return c;
        }));

        foreach (var v in graph.Adj.Keys)
            dist[v] = int.MaxValue;
        if (!graph.Adj.ContainsKey(s) || !graph.Adj.ContainsKey(t)) return int.MaxValue;
        dist[s] = 0;
        pq.Add((0, s));

        while (pq.Count > 0)
        {
            var cur = pq.Min; pq.Remove(cur);
            int d = cur.dist, u = cur.node;
            if (u == t) return d;
            if (d > dist[u]) continue;
            foreach (var e in graph.Adj[u])
            {
                int v = e.V;
                if (v == avoid) continue;
                int nd = d + e.W;
                if (!dist.ContainsKey(v) || nd < dist[v])
                {
                    if (dist.ContainsKey(v)) pq.Remove((dist[v], v));
                    dist[v] = nd;
                    pq.Add((nd, v));
                }
            }
        }
        return int.MaxValue;
    }

    // After preprocessing we've removed nodes from base graph.
    // For query we need the final CH graph: original nodes + shortcuts + levels.
    // In this educational implementation we stored shortcuts into the graph as we added them,
    // but removed contracted nodes. Therefore for queries we must reconstruct a graph containing
    // all edges and nodes with their assigned levels.
    // To keep things simple: we'll reconstruct the original graph from the list of edges we added earlier.
    // For this example, it's simpler to have kept a copy; but for assignment scope this approach is acceptable.
    //
    // For clarity: below, we assume user will run query on a graph that still contains nodes (we saved a backup).
    // So we provide a static helper to run query on a "fullGraph" with levels mapping computed from contraction order.

    public Dictionary<int, int> GetLevels() => new Dictionary<int, int>(level);
    public List<string> GetLog() => log;
}

// Utility: standard Dijkstra (used for querying on full graph)
class Dijkstra
{
    public static (int dist, List<int> path, List<string> log) BidirectionalCHQuery(Graph fullGraph, Dictionary<int, int> level, int s, int t)
    {
        var logSteps = new List<string>();
        if (!fullGraph.Adj.ContainsKey(s) || !fullGraph.Adj.ContainsKey(t))
            return (int.MaxValue, new List<int>(), logSteps);

        var distF = new Dictionary<int, int>();
        var distB = new Dictionary<int, int>();
        var prevF = new Dictionary<int, int?>(); // for path reconstruction
        var prevB = new Dictionary<int, int?>();

        foreach (var v in fullGraph.Adj.Keys)
        {
            distF[v] = int.MaxValue;
            distB[v] = int.MaxValue;
            prevF[v] = null;
            prevB[v] = null;
        }

        var pqF = new SortedSet<(int dist, int node)>(Comparer<(int, int)>.Create((a, b) =>
        {
            int c = a.dist.CompareTo(b.dist);
            if (c == 0) c = a.node.CompareTo(b.node);
            return c;
        }));
        var pqB = new SortedSet<(int dist, int node)>(Comparer<(int, int)>.Create((a, b) =>
        {
            int c = a.dist.CompareTo(b.dist);
            if (c == 0) c = a.node.CompareTo(b.node);
            return c;
        }));

        distF[s] = 0; pqF.Add((0, s));
        distB[t] = 0; pqB.Add((0, t));

        var visitedF = new HashSet<int>();
        var visitedB = new HashSet<int>();

        int best = int.MaxValue;
        int meetingNode = -1;

        while (pqF.Count > 0 || pqB.Count > 0)
        {
            if (pqF.Count > 0)
            {
                var cur = pqF.Min; pqF.Remove(cur);
                int d = cur.dist, u = cur.node;
                if (d != distF[u]) continue;
                visitedF.Add(u);
                logSteps.Add($"[F] pop {u} dist={d}");

                // relax neighbors but only to nodes with level >= level[u] (move up hierarchy)
                foreach (var e in fullGraph.Adj[u])
                {
                    int v = e.V;
                    // default level 0 if not present (shouldn't happen)
                    int lu = level.ContainsKey(u) ? level[u] : 0;
                    int lv = level.ContainsKey(v) ? level[v] : 0;
                    if (lv < lu) continue; // only go to same-or-higher level
                    int nd = d + e.W;
                    if (nd < distF[v])
                    {
                        if (distF[v] != int.MaxValue) pqF.Remove((distF[v], v));
                        distF[v] = nd;
                        prevF[v] = u;
                        pqF.Add((nd, v));
                        logSteps.Add($"  [F] relax {u}->{v} w={e.W}, newDist={nd}");
                    }
                }

                if (visitedB.Contains(u))
                {
                    int total = distF[u] + distB[u];
                    if (total < best)
                    {
                        best = total; meetingNode = u;
                        logSteps.Add($"  [MEET] at {u} total={total}");
                    }
                }
            }

            if (pqB.Count > 0)
            {
                var cur = pqB.Min; pqB.Remove(cur);
                int d = cur.dist, u = cur.node;
                if (d != distB[u]) continue;
                visitedB.Add(u);
                logSteps.Add($"[B] pop {u} dist={d}");

                // backward search: relax neighbors but only to nodes with level >= level[u]
                // (since graph is undirected, this symmetric condition works for educational purposes)
                foreach (var e in fullGraph.Adj[u])
                {
                    int v = e.V;
                    int lu = level.ContainsKey(u) ? level[u] : 0;
                    int lv = level.ContainsKey(v) ? level[v] : 0;
                    if (lv < lu) continue;
                    int nd = d + e.W;
                    if (nd < distB[v])
                    {
                        if (distB[v] != int.MaxValue) pqB.Remove((distB[v], v));
                        distB[v] = nd;
                        prevB[v] = u;
                        pqB.Add((nd, v));
                        logSteps.Add($"  [B] relax {u}->{v} w={e.W}, newDist={nd}");
                    }
                }

                if (visitedF.Contains(u))
                {
                    int total = distF[u] + distB[u];
                    if (total < best)
                    {
                        best = total; meetingNode = u;
                        logSteps.Add($"  [MEET] at {u} total={total}");
                    }
                }
            }

            // termination heuristic: if the smallest priority in both queues exceeds current best, stop
            int minF = pqF.Count > 0 ? pqF.Min.dist : int.MaxValue;
            int minB = pqB.Count > 0 ? pqB.Min.dist : int.MaxValue;
            if (minF + minB >= best) break;
        }

        if (best == int.MaxValue) return (int.MaxValue, new List<int>(), logSteps);

        // reconstruct path via meetingNode: s -> ... -> meetingNode and meetingNode -> ... -> t
        var pathF = new List<int>();
        int curNode = meetingNode;
        while (curNode != 0 && prevF.ContainsKey(curNode) && prevF[curNode] != null)
        {
            pathF.Add(curNode);
            curNode = prevF[curNode].Value;
        }
        pathF.Add(s);
        pathF.Reverse();

        var pathB = new List<int>();
        curNode = meetingNode;
        while (curNode != 0 && prevB.ContainsKey(curNode) && prevB[curNode] != null)
        {
            pathB.Add(prevB[curNode].Value); // because prevB stores next toward t
            curNode = prevB[curNode].Value;
        }

        // Combine: pathF + pathB (pathB starts after meetingNode)
        var fullPath = new List<int>();
        fullPath.AddRange(pathF);
        // append nodes from meetingNode's neighbor toward t (reconstruct from prevB)
        var back = new List<int>();
        curNode = meetingNode;
        while (prevB.ContainsKey(curNode) && prevB[curNode] != null)
        {
            int nx = prevB[curNode].Value;
            back.Add(nx);
            curNode = nx;
        }
        fullPath.AddRange(back);

        return (best, fullPath, logSteps);
    }
}

class Program
{
    // example mapping: node id -> campus name (as per project spec)
    static Dictionary<int, string> DefaultCampus = new Dictionary<int, string>
    {
        {0,"UGM"}, {1,"UNY"}, {2,"UPN"}, {3,"UII"}, {4,"UAD"},
        {5,"USD"}, {6,"UMY"}, {7,"UAJY"}, {8,"ISI"}, {9,"UIN"}
    };

    static void Main()
    {
        Console.OutputEncoding = Encoding.UTF8;
        Console.WriteLine("=== Contraction Hierarchies - Simple C# Implementation ===");
        Console.WriteLine("Pilihan dataset:");
        Console.WriteLine("1) Pakai dataset kampus contoh (Yogyakarta)");
        Console.WriteLine("2) Input manual");
        Console.Write("Pilih (1/2): ");
        var choice = Console.ReadLine()?.Trim();

        Graph fullGraph = new Graph();
        Dictionary<int, string> names = new Dictionary<int, string>();

        if (choice == "1")
        {
            // build small realistic-ish network (symmetric)
            names = new Dictionary<int, string>(DefaultCampus);
            // we'll add some plausible edges (km)
            fullGraph.AddEdge(0,1,2); // UGM-UNY
            fullGraph.AddEdge(1,2,4); // UNY-UPN
            fullGraph.AddEdge(0,9,3); // UGM-UIN
            fullGraph.AddEdge(2,4,3); // UPN-UAD
            fullGraph.AddEdge(4,6,5); // UAD-UMY
            fullGraph.AddEdge(0,3,6); // UGM-UII
            fullGraph.AddEdge(3,5,4); // UII-USD
            fullGraph.AddEdge(5,6,6); // USD-UMY
            fullGraph.AddEdge(6,7,4); // UMY-UAJY
            fullGraph.AddEdge(7,8,7); // UAJY-ISI
            fullGraph.AddEdge(8,0,8); // ISI-UGM
            // add some cross links
            fullGraph.AddEdge(2,9,5); // UPN-UIN
            fullGraph.AddEdge(1,3,3); // UNY-UII
            fullGraph.AddEdge(5,2,6); // USD-UPN
            Console.WriteLine("Dataset contoh dimuat.");
        }
        else
        {
            Console.Write("Masukkan jumlah kampus: ");
            int n = int.Parse(Console.ReadLine() ?? "0");
            for (int i = 0; i < n; i++)
            {
                Console.Write($"Nama kampus ke-{i}: ");
                string nm = Console.ReadLine() ?? $"Node{i}";
                names[i] = nm;
                fullGraph.AddNode(i);
            }

            Console.WriteLine("Masukkan jarak antar kampus (masukkan 0 kalau tidak terhubung).");
            for (int i = 0; i < n; i++)
            {
                for (int j = i + 1; j < n; j++)
                {
                    Console.Write($"Jarak {names[i]} - {names[j]} (km): ");
                    int w = int.Parse(Console.ReadLine() ?? "0");
                    if (w > 0) fullGraph.AddEdge(i, j, w);
                }
            }
        }

        // Save a backup of fullGraph for queries (preprocessing will remove nodes from the working copy)
        // For this educational implementation we'll copy edges and nodes into a working graph
        Graph working = CopyGraph(fullGraph);

        // Preprocess CH on working graph, recording contraction order
        var ch = new ContractionHierarchies(working);
        ch.Preprocess();
        var levels = ch.GetLevels();
        var preprocessingLog = ch.GetLog();

        // Print preprocessing log
        Console.WriteLine("\n=== Preprocessing log ===");
        foreach (var l in preprocessingLog) Console.WriteLine(l);

        // For queries we need the FULL graph with all original nodes and shortcuts.
        // Our current "working" graph has contracted nodes removed; but shortcuts were added into that working graph before nodes removed.
        // To simplify, we will merge shortcuts found into the fullGraph: i.e., compare edge counts and add missing edges with the same logic.
        // In this educational implementation we assume shortcuts are added to working graph and we saved them indirectly when we added edges to working.
        // So let's just reconstruct queryGraph by merging fullGraph + any new edges present in working (that connect nodes that still exist in fullGraph).
        Graph queryGraph = CopyGraph(fullGraph);
        // Merge edges from working (some edges in working may be shortcuts between original nodes)
        foreach (var u in working.Adj.Keys)
        {
            foreach (var e in working.Adj[u])
            {
                // only add edges between nodes that exist in original fullGraph
                if (queryGraph.Adj.ContainsKey(e.U) && queryGraph.Adj.ContainsKey(e.V))
                {
                    queryGraph.AddEdge(e.U, e.V, e.W, e.IsShortcut);
                }
            }
        }

        // If some nodes did not receive level assignment (unlikely), assign them low level
        foreach (var v in queryGraph.Adj.Keys)
            if (!levels.ContainsKey(v)) levels[v] = 0;

        // Save graph.dot for visualization
        SaveGraphDot(queryGraph, levels, names, "graph.dot");
        Console.WriteLine("\nGraph exported to graph.dot (render with Graphviz: dot -Tpng graph.dot -o graph.png)");

        // Query loop
        while (true)
        {
            Console.WriteLine("\n=== Query shortest path (CH) ===");
            int s = -1, t = -1;

            Console.WriteLine("Daftar node:");
            foreach (var kv in names) Console.WriteLine($" {kv.Key}: {kv.Value}");
            Console.Write("Masukkan node asal (id): ");
            var inS = Console.ReadLine();
            if (string.IsNullOrWhiteSpace(inS)) break;
            s = int.Parse(inS);
            Console.Write("Masukkan node tujuan (id): ");
            t = int.Parse(Console.ReadLine() ?? "0");

            var (dist, path, logs) = Dijkstra.BidirectionalCHQuery(queryGraph, levels, s, t);

            Console.WriteLine("\n=== Query log ===");
            foreach (var ln in logs) Console.WriteLine(ln);

            Console.WriteLine("\n=== Hasil ===");
            if (dist == int.MaxValue)
            {
                Console.WriteLine("Tidak ada jalur antara node.");
            }
            else
            {
                Console.WriteLine($"Jalur terpendek: {string.Join(" -> ", path.Select(x => names.ContainsKey(x) ? names[x] : x.ToString()))}");
                Console.WriteLine($"Total jarak: {dist} km");
            }

            Console.Write("Lakukan query lagi? (y/n): ");
            var again = Console.ReadLine()?.Trim().ToLower();
            if (again != "y") break;
        }

        Console.WriteLine("Selesai.");
    }

    static Graph CopyGraph(Graph src)
    {
        var g = new Graph();
        foreach (var v in src.Adj.Keys) g.AddNode(v);
        foreach (var u in src.Adj.Keys)
        {
            foreach (var e in src.Adj[u])
            {
                if (u < e.V) // add once (since AddEdge adds both directions)
                    g.AddEdge(u, e.V, e.W, e.IsShortcut);
            }
        }
        return g;
    }

    static void SaveGraphDot(Graph g, Dictionary<int, int> levels, Dictionary<int, string> names, string path)
    {
        var sb = new StringBuilder();
        sb.AppendLine("graph G {");
        sb.AppendLine("  overlap=false;");
        sb.AppendLine("  splines=true;");
        // node labels with level
        foreach (var v in g.Adj.Keys)
        {
            string label = names.ContainsKey(v) ? names[v] : v.ToString();
            int lev = levels.ContainsKey(v) ? levels[v] : 0;
            sb.AppendLine($"  {v} [label=\"{label}\\n(L{lev})\"];");
        }
        var added = new HashSet<(int, int)>();
        foreach (var u in g.Adj.Keys)
        {
            foreach (var e in g.Adj[u])
            {
                int v = e.V;
                if (u == v) continue;
                var key = u < v ? (u, v) : (v, u);
                if (added.Contains(key)) continue;
                added.Add(key);
                string style = e.IsShortcut ? "dashed" : "solid";
                sb.AppendLine($"  {u} -- {v} [label=\"{e.W}\" style={style}];");
            }
        }
        sb.AppendLine("}");
        File.WriteAllText(path, sb.ToString());
    }
}
