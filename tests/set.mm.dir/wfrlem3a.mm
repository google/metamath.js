include "cv.mm"
include "wfn.mm"
include "wss.mm"
include "cpred.mm"
include "wral.mm"
include "wa.mm"
include "cfv.mm"
include "cres.mm"
include "wceq.mm"
include "w3a.mm"
include "wex.mm"
include "fneq1.mm"
include "fveq1.mm"
include "reseq1.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "ralbidv.mm"
include "3anbi13d.mm"
include "exbidv.mm"
include "wfrlem1.mm"
include "elab2.mm"

theorem wfrlem3a
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cR: class R
  let vf: setvar f
  let cF: class F
  let cG: class G
  let vg: setvar g
  assume wfrlem1.1: |- B = { f | E. x ( f Fn x /\ ( x C_ A /\ A. y e. x Pred ( R , A , y ) C_ x ) /\ A. y e. x ( f ` y ) = ( F ` ( f |` Pred ( R , A , y ) ) ) ) }
  assume wfrlem3a.2: |- G e. _V

  disjoint A f
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F f
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint R f
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint G f
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint G w
  disjoint A g
  disjoint f g
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint F g
  disjoint R g
  disjoint G g
  assert |- ( G e. B <-> E. z ( G Fn z /\ ( z C_ A /\ A. w e. z Pred ( R , A , w ) C_ z ) /\ A. w e. z ( G ` w ) = ( F ` ( G |` Pred ( R , A , w ) ) ) ) )

  proof
    vg
    cv
    #
    vz
    cv
    #
    wfn
    #
    @1
    cA
    wss
    cA
    cR
    vw
    cv
    #
    cpred
    #
    @1
    wss
    vw
    @1
    wral
    wa
    #
    @3
    @0
    cfv
    #
    @0
    @4
    cres
    #
    cF
    cfv
    #
    wceq
    #
    vw
    @1
    wral
    #
    w3a
    #
    vz
    wex
    cG
    @1
    wfn
    #
    @5
    @3
    cG
    cfv
    #
    cG
    @4
    cres
    #
    cF
    cfv
    #
    wceq
    #
    vw
    @1
    wral
    #
    w3a
    #
    vz
    wex
    vg
    cG
    cB
    wfrlem3a.2
    @0
    cG
    wceq
    #
    @11
    @18
    vz
    @19
    @2
    @12
    @10
    @17
    @5
    @1
    @0
    cG
    fneq1
    @19
    @9
    @16
    vw
    @1
    @19
    @6
    @13
    @8
    @15
    @3
    @0
    cG
    fveq1
    @19
    @7
    @14
    cF
    @0
    cG
    @4
    reseq1
    fveq2d
    eqeq12d
    ralbidv
    3anbi13d
    exbidv
    vx
    vy
    vz
    vw
    cA
    cB
    cR
    vf
    vg
    cF
    wfrlem1.1
    wfrlem1
    elab2
end
