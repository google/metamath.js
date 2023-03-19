include "cc.mm"
include "wss.mm"
include "wa.mm"
include "ccncf.mm"
include "co.mm"
include "wcel.mm"
include "wi.mm"
include "wtru.mm"
include "wf.mm"
include "a1i.mm"
include "cv.mm"
include "crp.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "elcncf1di.mm"
include "trud.mm"

theorem elcncf1ii
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cF: class F
  let cZ: class Z
  assume elcncf1i.1: |- F : A --> B
  assume elcncf1i.2: |- ( ( x e. A /\ y e. RR+ ) -> Z e. RR+ )
  assume elcncf1i.3: |- ( ( ( x e. A /\ w e. A ) /\ y e. RR+ ) -> ( ( abs ` ( x - w ) ) < Z -> ( abs ` ( ( F ` x ) - ( F ` w ) ) ) < y ) )

  disjoint w x
  disjoint w y
  disjoint A w
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint Z w
  assert |- ( ( A C_ CC /\ B C_ CC ) -> F e. ( A -cn-> B ) )

  proof
    cA
    cc
    wss
    cB
    cc
    wss
    wa
    cF
    cA
    cB
    ccncf
    co
    wcel
    wi
    wtru
    vx
    vy
    vw
    cA
    cB
    cF
    cZ
    cA
    cB
    cF
    wf
    wtru
    elcncf1i.1
    a1i
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    crp
    wcel
    #
    wa
    cZ
    crp
    wcel
    wi
    wtru
    elcncf1i.2
    a1i
    @1
    vw
    cv
    #
    cA
    wcel
    wa
    @3
    wa
    @0
    @4
    cmin
    co
    cabs
    cfv
    cZ
    clt
    wbr
    @0
    cF
    cfv
    @4
    cF
    cfv
    cmin
    co
    cabs
    cfv
    @2
    clt
    wbr
    wi
    wi
    wtru
    elcncf1i.3
    a1i
    elcncf1di
    trud
end
