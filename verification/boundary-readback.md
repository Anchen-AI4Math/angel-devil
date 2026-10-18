# Blind statement readback

Auditor: independent `boundary_readback` agent, fresh context; given only the
Lean declarations (without source comments) and the Prove2Me auditor instructions.
Target: `AngelDevil.connectedSquares_perimeter`.

For every finite set \(S\subseteq\mathbb Z^2\), assume that \(S\) is nonempty and that for every \(a,b\in S\) there is a finite sequence \(a=p_0,p_1,\ldots,p_k=b\), with \(k\ge 0\), whose consecutive points both belong to \(S\) and differ by one of \((1,0),(-1,0),(0,1),(0,-1)\); a sequence of length zero is permitted when \(a=b\). For each \(v=(x,y)\in S\), count how many of the four points \((x+1,y),(x-1,y),(x,y+1),(x,y-1)\) do not belong to \(S\), and let \(P(S)\) be the sum of these counts over all \(v\in S\). Then \(P(S)\le 2|S|+2\), as an inequality of natural numbers. Each missing neighbor contributes separately, including missing neighbors in any enclosed gaps; no distinction is made between an outer boundary and boundaries of holes. The empty set is excluded by the hypothesis, while singleton sets are included and have \(P(S)=4=2|S|+2\); diagonal contact alone does not supply a step in the required connecting sequences.

## Source comparison by the main agent

Matches Mathe's Definition 4.1 and Claim 4.2 (author manuscript p. 6): finite,
nonempty sets connected by shared sides. Counting an occupied square together
with a direction to an unoccupied neighbor counts each exposed unit side once.
This does not establish that the runner's wall supports are connected, that its
walls are distinct, or that it escapes. Those obligations remain in Theorem 4.5.
