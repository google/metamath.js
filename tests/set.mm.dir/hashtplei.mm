include "cpr.mm"
include "csn.mm"
include "ctp.mm"
include "c2.mm"
include "c1.mm"
include "c3.mm"
include "df-tp.mm"
include "hashprlei.mm"
include "hashsnlei.mm"
include "2nn0.mm"
include "1nn0.mm"
include "2p1e3.mm"
include "hashunlei.mm"

theorem hashtplei
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( { A , B , C } e. Fin /\ ( # ` { A , B , C } ) <_ 3 )

  proof
    cA
    cB
    cpr
    cC
    csn
    cA
    cB
    cC
    ctp
    c2
    c1
    c3
    cA
    cB
    cC
    df-tp
    cA
    cB
    hashprlei
    cC
    hashsnlei
    2nn0
    1nn0
    2p1e3
    hashunlei
end
