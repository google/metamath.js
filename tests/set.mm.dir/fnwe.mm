include "cv.mm"
include "cxp.mm"
include "wcel.mm"
include "wa.mm"
include "c1st.mm"
include "cfv.mm"
include "wbr.mm"
include "wceq.mm"
include "c2nd.mm"
include "wo.mm"
include "copab.mm"
include "cop.mm"
include "cmpt.mm"
include "eqid.mm"
include "fnwelem.mm"

theorem fnwe
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  let cG: class G
  let cQ: class Q
  assume fnwe.1: |- T = { <. x , y >. | ( ( x e. A /\ y e. A ) /\ ( ( F ` x ) R ( F ` y ) \/ ( ( F ` x ) = ( F ` y ) /\ x S y ) ) ) }
  assume fnwe.2: |- ( ph -> F : A --> B )
  assume fnwe.3: |- ( ph -> R We B )
  assume fnwe.4: |- ( ph -> S We A )
  assume fnwe.5: |- ( ph -> ( F " w ) e. _V )

  disjoint w x
  disjoint w y
  disjoint A w
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint ph w
  disjoint ph x
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint T w
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w z
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B u
  disjoint B v
  disjoint B z
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint ph z
  disjoint F u
  disjoint F v
  disjoint F z
  disjoint Q w
  disjoint Q x
  disjoint Q y
  disjoint R u
  disjoint R v
  disjoint S u
  disjoint S v
  assert |- ( ph -> T We A )

  proof
    wph
    vx
    vy
    vz
    vw
    vv
    vu
    cA
    cB
    vu
    cv
    #
    cB
    cA
    cxp
    #
    wcel
    vv
    cv
    #
    @1
    wcel
    wa
    @0
    c1st
    cfv
    #
    @2
    c1st
    cfv
    #
    cR
    wbr
    @3
    @4
    wceq
    @0
    c2nd
    cfv
    @2
    c2nd
    cfv
    cS
    wbr
    wa
    wo
    wa
    vu
    vv
    copab
    #
    cR
    cS
    cT
    cF
    vz
    cA
    vz
    cv
    #
    cF
    cfv
    @6
    cop
    cmpt
    #
    fnwe.1
    fnwe.2
    fnwe.3
    fnwe.4
    fnwe.5
    @5
    eqid
    @7
    eqid
    fnwelem
end
