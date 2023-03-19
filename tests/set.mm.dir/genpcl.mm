include "cnp.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "co.mm"
include "wpss.mm"
include "cnq.mm"
include "cv.mm"
include "cltq.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "wrex.mm"
include "wral.mm"
include "genpn0.mm"
include "wss.mm"
include "wceq.mm"
include "wn.mm"
include "genpss.mm"
include "vex.mm"
include "caovord.mm"
include "genpnnp.mm"
include "dfpss2.mm"
include "sylanbrc.mm"
include "genpcd.mm"
include "alrimdv.mm"
include "caovcom.mm"
include "genpnmax.mm"
include "jcad.mm"
include "ralrimiv.mm"
include "jca31.mm"
include "elnp.mm"
include "sylibr.mm"

theorem genpcl
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cF: class F
  let cG: class G
  let cC: class C
  let cD: class D
  assume genp.1: |- F = ( w e. P. , v e. P. |-> { x | E. y e. w E. z e. v x = ( y G z ) } )
  assume genp.2: |- ( ( y e. Q. /\ z e. Q. ) -> ( y G z ) e. Q. )
  assume genpcl.3: |- ( h e. Q. -> ( f <Q g <-> ( h G f ) <Q ( h G g ) ) )
  assume genpcl.4: |- ( x G y ) = ( y G x )
  assume genpcl.5: |- ( ( ( ( A e. P. /\ g e. A ) /\ ( B e. P. /\ h e. B ) ) /\ x e. Q. ) -> ( x <Q ( g G h ) -> x e. ( A F B ) ) )

  disjoint v w
  disjoint A w
  disjoint A v
  disjoint B w
  disjoint B v
  disjoint x y
  disjoint w x
  disjoint v x
  disjoint h x
  disjoint F x
  disjoint w y
  disjoint v y
  disjoint h y
  disjoint F y
  disjoint h w
  disjoint F w
  disjoint h v
  disjoint F v
  disjoint F h
  disjoint x y
  disjoint x z
  disjoint f x
  disjoint g x
  disjoint h x
  disjoint A x
  disjoint y z
  disjoint f y
  disjoint g y
  disjoint h y
  disjoint A y
  disjoint f z
  disjoint g z
  disjoint h z
  disjoint A z
  disjoint f g
  disjoint f h
  disjoint A f
  disjoint g h
  disjoint A g
  disjoint A h
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint B f
  disjoint B g
  disjoint B h
  disjoint w x
  disjoint v x
  disjoint G x
  disjoint w y
  disjoint v y
  disjoint G y
  disjoint w z
  disjoint v z
  disjoint G z
  disjoint v w
  disjoint f w
  disjoint g w
  disjoint h w
  disjoint G w
  disjoint f v
  disjoint g v
  disjoint h v
  disjoint G v
  disjoint G f
  disjoint G g
  disjoint G h
  disjoint F f
  disjoint F g
  disjoint C f
  disjoint C g
  disjoint C h
  disjoint D g
  disjoint D h
  assert |- ( ( A e. P. /\ B e. P. ) -> ( A F B ) e. P. )

  proof
    cA
    cnp
    wcel
    cB
    cnp
    wcel
    wa
    #
    c0
    cA
    cB
    cF
    co
    #
    wpss
    #
    @1
    cnq
    wpss
    #
    wa
    vx
    cv
    #
    vf
    cv
    #
    cltq
    wbr
    @4
    @1
    wcel
    wi
    #
    vx
    wal
    #
    @5
    @4
    cltq
    wbr
    vx
    @1
    wrex
    #
    wa
    #
    vf
    @1
    wral
    #
    wa
    @1
    cnp
    wcel
    @0
    @2
    @3
    @10
    vx
    vy
    vz
    vw
    vv
    cA
    cB
    cF
    cG
    genp.1
    genp.2
    genpn0
    @0
    @1
    cnq
    wss
    @1
    cnq
    wceq
    wn
    @3
    vx
    vy
    vz
    vw
    vv
    cA
    cB
    cF
    cG
    genp.1
    genp.2
    genpss
    vx
    vy
    vz
    vw
    vv
    cA
    cB
    cF
    cG
    genp.1
    genp.2
    vf
    vg
    vh
    @4
    vy
    cv
    vz
    cv
    #
    cltq
    cnq
    cG
    vx
    vex
    vy
    vex
    genpcl.3
    caovord
    genpcl.4
    genpnnp
    @1
    cnq
    dfpss2
    sylanbrc
    @0
    @9
    vf
    @1
    @0
    @5
    @1
    wcel
    #
    @7
    @8
    @0
    @12
    @6
    vx
    vx
    vy
    vz
    vw
    vv
    cA
    cB
    vf
    vg
    vh
    cF
    cG
    genp.1
    genp.2
    genpcl.5
    genpcd
    alrimdv
    vx
    vy
    vz
    vw
    vv
    cA
    cB
    vf
    cF
    cG
    genp.1
    genp.2
    vf
    vg
    vh
    @11
    vw
    cv
    #
    vv
    cv
    cltq
    cnq
    cG
    vz
    vex
    #
    vw
    vex
    #
    genpcl.3
    caovord
    vx
    vy
    @11
    @13
    cG
    @14
    @15
    genpcl.4
    caovcom
    genpnmax
    jcad
    ralrimiv
    jca31
    vf
    vx
    @1
    elnp
    sylibr
end
