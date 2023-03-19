include "cxr.mm"
include "wss.mm"
include "clt.mm"
include "wor.mm"
include "xrltso.mm"
include "a1i.mm"
include "xrinfmss.mm"
include "id.mm"
include "infglbb.mm"

theorem infxrglb
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint B x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  assert |- ( ( A C_ RR* /\ B e. RR* ) -> ( inf ( A , RR* , < ) < B <-> E. x e. A x < B ) )

  proof
    cA
    cxr
    wss
    #
    vz
    vy
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
    vz
    vy
    vx
    cA
    xrinfmss
    @0
    id
    infglbb
end
