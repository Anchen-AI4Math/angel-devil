We prove that five burns suffice to prepare a line guard from an empty line.

The king's horizontal coordinate changes by -1, 0, or 1 after each burn. A preparation tree chooses a burn, branches on those three displacements, and after four such displacements chooses a fifth burn completing the triple at the king's current coordinate. This is the local argument illustrated in Kutz, Chapter 1, Section 1.1, Figure 2.

The submitted proof supplies the burn at every node and checks every branch in Lean. Each leaf checks the three required memberships in the five chosen sites. Python only generated the witnesses; no Python answer, external solver result, or native evaluation axiom is assumed.
