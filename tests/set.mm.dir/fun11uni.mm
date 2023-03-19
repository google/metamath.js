include "cv.mm"
include "wfun.mm"
include "ccnv.mm"
include "wa.mm"
include "wss.mm"
include "wo.mm"
include "wral.mm"
include "cuni.mm"
include "simpl.mm"
include "anim1i.mm"
include "ralimi.mm"
include "fununi.mm"
include "syl.mm"
include "simpr.mm"
include "funcnvuni.mm"
include "jca.mm"

theorem fun11uni
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v

  disjoint f g
  disjoint A f
  disjoint A g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint f w
  disjoint f v
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint g w
  disjoint g v
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint A x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint A y
  disjoint w z
  disjoint v z
  disjoint A z
  disjoint v w
  disjoint A w
  disjoint A v
  assert |- ( A. f e. A ( ( Fun f /\ Fun `' f ) /\ A. g e. A ( f C_ g \/ g C_ f ) ) -> ( Fun U. A /\ Fun `' U. A ) )

  proof
    vf
    cv
    #
    wfun
    #
    @0
    ccnv
    wfun
    #
    wa
    #
    @0
    vg
    cv
    #
    wss
    @4
    @0
    wss
    wo
    vg
    cA
    wral
    #
    wa
    #
    vf
    cA
    wral
    #
    cA
    cuni
    #
    wfun
    #
    @8
    ccnv
    wfun
    #
    @7
    @1
    @5
    wa
    #
    vf
    cA
    wral
    @9
    @6
    @11
    vf
    cA
    @3
    @1
    @5
    @1
    @2
    simpl
    anim1i
    ralimi
    cA
    vf
    vg
    fununi
    syl
    @7
    @2
    @5
    wa
    #
    vf
    cA
    wral
    @10
    @6
    @12
    vf
    cA
    @3
    @2
    @5
    @1
    @2
    simpr
    anim1i
    ralimi
    cA
    vf
    vg
    funcnvuni
    syl
    jca
end
