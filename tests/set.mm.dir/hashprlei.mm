include "csn.mm"
include "cpr.mm"
include "c1.mm"
include "c2.mm"
include "df-pr.mm"
include "hashsnlei.mm"
include "1nn0.mm"
include "1p1e2.mm"
include "hashunlei.mm"

theorem hashprlei
  let cA: class A
  let cB: class B


  assert |- ( { A , B } e. Fin /\ ( # ` { A , B } ) <_ 2 )

  proof
    cA
    csn
    cB
    csn
    cA
    cB
    cpr
    c1
    c1
    c2
    cA
    cB
    df-pr
    cA
    hashsnlei
    cB
    hashsnlei
    1nn0
    1nn0
    1p1e2
    hashunlei
end
