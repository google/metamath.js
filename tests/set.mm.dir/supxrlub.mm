include "cxr.mm"
include "wss.mm"
include "clt.mm"
include "wor.mm"
include "xrltso.mm"
include "a1i.mm"
include "xrsupss.mm"
include "id.mm"
include "suplub2.mm"

theorem supxrlub
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint A y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint B y
  disjoint B z
  disjoint B w
  assert |- ( ( A C_ RR* /\ B e. RR* ) -> ( B < sup ( A , RR* , < ) <-> E. x e. A B < x ) )

  proof
    cA
    cxr
    wss
    #
    vy
    vz
    vx
    cxr
    cA
    cB
    clt
    cxr
    clt
    wor
    @0
    xrltso
    a1i
    vy
    vz
    vx
    cA
    xrsupss
    @0
    id
    suplub2
end
