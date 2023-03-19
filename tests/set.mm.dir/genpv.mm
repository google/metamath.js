include "cnp.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "oveq1.mm"
include "rexeq.mm"
include "abbidv.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "rexbidv.mm"
include "cvv.mm"
include "cnq.mm"
include "wss.mm"
include "wi.mm"
include "elprnq.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "syl2an.mm"
include "an4s.mm"
include "rexlimdvva.mm"
include "abssdv.mm"
include "nqex.mm"
include "ssexg.mm"
include "sylancl.mm"
include "weq.mm"
include "ovmpt2g.mm"
include "mpd3an3.mm"
include "vtocl2ga.mm"
include "eqeq1.mm"
include "2rexbidv.mm"
include "eqeq2d.mm"
include "cbvrex2v.mm"
include "syl6bb.mm"
include "cbvabv.mm"
include "syl6eq.mm"

theorem genpv
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
  assert |- ( ( A e. P. /\ B e. P. ) -> ( A F B ) = { f | E. g e. A E. h e. B f = ( g G h ) } )

  proof
    cA
    cnp
    wcel
    cB
    cnp
    wcel
    wa
    cA
    cB
    cF
    co
    #
    vx
    cv
    #
    vy
    cv
    #
    vz
    cv
    #
    cG
    co
    #
    wceq
    #
    vz
    cB
    wrex
    #
    vy
    cA
    wrex
    #
    vx
    cab
    #
    vf
    cv
    #
    vg
    cv
    #
    vh
    cv
    #
    cG
    co
    #
    wceq
    #
    vh
    cB
    wrex
    vg
    cA
    wrex
    #
    vf
    cab
    @9
    @10
    cF
    co
    #
    @5
    vz
    @10
    wrex
    #
    vy
    @9
    wrex
    #
    vx
    cab
    #
    wceq
    #
    cA
    @10
    cF
    co
    #
    @16
    vy
    cA
    wrex
    #
    vx
    cab
    #
    wceq
    @0
    @8
    wceq
    vf
    vg
    cA
    cB
    cnp
    cnp
    @9
    cA
    wceq
    #
    @15
    @20
    @18
    @22
    @9
    cA
    @10
    cF
    oveq1
    @23
    @17
    @21
    vx
    @16
    vy
    @9
    cA
    rexeq
    abbidv
    eqeq12d
    @10
    cB
    wceq
    #
    @20
    @0
    @22
    @8
    @10
    cB
    cA
    cF
    oveq2
    @24
    @21
    @7
    vx
    @24
    @16
    @6
    vy
    cA
    @5
    vz
    @10
    cB
    rexeq
    rexbidv
    abbidv
    eqeq12d
    @9
    cnp
    wcel
    #
    @10
    cnp
    wcel
    #
    @18
    cvv
    wcel
    #
    @19
    @25
    @26
    wa
    #
    @18
    cnq
    wss
    cnq
    cvv
    wcel
    @27
    @28
    @17
    vx
    cnq
    @28
    @5
    @1
    cnq
    wcel
    #
    vy
    vz
    @9
    @10
    @25
    @2
    @9
    wcel
    #
    @26
    @3
    @10
    wcel
    #
    @5
    @29
    wi
    #
    @25
    @30
    wa
    @2
    cnq
    wcel
    #
    @3
    cnq
    wcel
    #
    @32
    @26
    @31
    wa
    @9
    @2
    elprnq
    @10
    @3
    elprnq
    @33
    @34
    wa
    @29
    @5
    @4
    cnq
    wcel
    genp.2
    @1
    @4
    cnq
    eleq1
    syl5ibrcom
    syl2an
    an4s
    rexlimdvva
    abssdv
    nqex
    @18
    cnq
    cvv
    ssexg
    sylancl
    vw
    vv
    @9
    @10
    cnp
    cnp
    @5
    vz
    vv
    cv
    #
    wrex
    #
    vy
    vw
    cv
    #
    wrex
    #
    vx
    cab
    @18
    cF
    @36
    vy
    @9
    wrex
    #
    vx
    cab
    cvv
    vw
    vf
    weq
    @38
    @39
    vx
    @36
    vy
    @37
    @9
    rexeq
    abbidv
    vv
    vg
    weq
    #
    @39
    @17
    vx
    @40
    @36
    @16
    vy
    @9
    @5
    vz
    @35
    @10
    rexeq
    rexbidv
    abbidv
    genp.1
    ovmpt2g
    mpd3an3
    vtocl2ga
    @7
    @14
    vx
    vf
    vx
    vf
    weq
    #
    @7
    @9
    @4
    wceq
    #
    vz
    cB
    wrex
    vy
    cA
    wrex
    @14
    @41
    @5
    @42
    vy
    vz
    cA
    cB
    @1
    @9
    @4
    eqeq1
    2rexbidv
    @42
    @13
    @9
    @10
    @3
    cG
    co
    #
    wceq
    vy
    vz
    vg
    vh
    cA
    cB
    vy
    vg
    weq
    @4
    @43
    @9
    @2
    @10
    @3
    cG
    oveq1
    eqeq2d
    vz
    vh
    weq
    @43
    @12
    @9
    @3
    @11
    @10
    cG
    oveq2
    eqeq2d
    cbvrex2v
    syl6bb
    cbvabv
    syl6eq
end
