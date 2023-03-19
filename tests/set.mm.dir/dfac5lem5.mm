include "cv.mm"
include "cin.mm"
include "wcel.mm"
include "weu.mm"
include "wral.mm"
include "wex.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "wi.mm"
include "dfac5lem4.mm"
include "wa.mm"
include "cop.mm"
include "simpr.mm"
include "a1i.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "ineq1.mm"
include "eleq2d.mm"
include "eubidv.mm"
include "rspccv.mm"
include "dfac5lem3.mm"
include "dfac5lem1.mm"
include "3imtr3g.mm"
include "jcad.mm"
include "cuni.mm"
include "eleq2i.mm"
include "elin.mm"
include "dfac5lem2.mm"
include "anbi1i.mm"
include "anass.mm"
include "bitri.mm"
include "3bitri.mm"
include "eubii.mm"
include "euanv.mm"
include "bitr2i.mm"
include "syl6ib.mm"
include "euex.mm"
include "nfeu1.mm"
include "nfv.mm"
include "nfim.mm"
include "simprbi.mm"
include "simpld.mm"
include "tz6.12.mm"
include "eleq1d.mm"
include "biimparc.mm"
include "exp32.mm"
include "mpcom.mm"
include "exlimi.mm"
include "syl6.mm"
include "expcomd.mm"
include "ralrimiv.mm"
include "cvv.mm"
include "vex.mm"
include "inex2.mm"
include "eqeltri.mm"
include "fveq1.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "spcev.mm"
include "syl.mm"
include "exlimiv.mm"

theorem dfac5lem5
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vh: setvar h
  let vg: setvar g
  assume dfac5lem.1: |- A = { u | ( u =/= (/) /\ E. t e. h u = ( { t } X. t ) ) }
  assume dfac5lem.2: |- B = ( U. A i^i y )
  assume dfac5lem.3: |- ( ph <-> A. x ( ( A. z e. x z =/= (/) /\ A. z e. x A. w e. x ( z =/= w -> ( z i^i w ) = (/) ) ) -> E. y A. z e. x E! v v e. ( z i^i y ) ) )

  disjoint f x
  disjoint f z
  disjoint f y
  disjoint f w
  disjoint f v
  disjoint f u
  disjoint f t
  disjoint f h
  disjoint x z
  disjoint x y
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint t x
  disjoint h x
  disjoint y z
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint t z
  disjoint h z
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint t y
  disjoint h y
  disjoint v w
  disjoint u w
  disjoint t w
  disjoint h w
  disjoint u v
  disjoint t v
  disjoint h v
  disjoint t u
  disjoint h u
  disjoint h t
  disjoint B z
  disjoint B w
  disjoint B f
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint A w
  disjoint f g
  disjoint g x
  disjoint g z
  disjoint g y
  disjoint g w
  disjoint g v
  disjoint g u
  disjoint g t
  disjoint g h
  disjoint B g
  disjoint A g
  assert |- ( ph -> E. f A. w e. h ( w =/= (/) -> ( f ` w ) e. w ) )

  proof
    wph
    vv
    cv
    #
    vz
    cv
    #
    vy
    cv
    #
    cin
    #
    wcel
    #
    vv
    weu
    #
    vz
    cA
    wral
    #
    vy
    wex
    vw
    cv
    #
    c0
    wne
    #
    @7
    vf
    cv
    #
    cfv
    #
    @7
    wcel
    #
    wi
    #
    vw
    vh
    cv
    #
    wral
    #
    vf
    wex
    #
    wph
    vx
    vy
    vz
    vw
    vv
    vu
    vt
    cA
    cB
    vh
    dfac5lem.1
    dfac5lem.2
    dfac5lem.3
    dfac5lem4
    @6
    @15
    vy
    @6
    @8
    @7
    cB
    cfv
    #
    @7
    wcel
    #
    wi
    #
    vw
    @13
    wral
    #
    @15
    @6
    @18
    vw
    @13
    @6
    @8
    @7
    @13
    wcel
    #
    @17
    @6
    @8
    @20
    wa
    #
    @7
    vg
    cv
    #
    cop
    #
    cB
    wcel
    #
    vg
    weu
    #
    @17
    @6
    @21
    @20
    @22
    @7
    wcel
    #
    @23
    @2
    wcel
    #
    wa
    #
    vg
    weu
    #
    wa
    #
    @25
    @6
    @21
    @20
    @29
    @21
    @20
    wi
    @6
    @8
    @20
    simpr
    a1i
    @6
    @7
    csn
    @7
    cxp
    #
    cA
    wcel
    @0
    @31
    @2
    cin
    #
    wcel
    #
    vv
    weu
    #
    @21
    @29
    @5
    @34
    vz
    @31
    cA
    @1
    @31
    wceq
    #
    @4
    @33
    vv
    @35
    @3
    @32
    @0
    @1
    @31
    @2
    ineq1
    eleq2d
    eubidv
    rspccv
    vw
    vu
    vt
    cA
    vh
    dfac5lem.1
    dfac5lem3
    vy
    vw
    vv
    vg
    dfac5lem1
    3imtr3g
    jcad
    @25
    @20
    @28
    wa
    #
    vg
    weu
    @30
    @24
    @36
    vg
    @24
    @23
    cA
    cuni
    #
    @2
    cin
    #
    wcel
    @23
    @37
    wcel
    #
    @27
    wa
    #
    @36
    cB
    @38
    @23
    dfac5lem.2
    eleq2i
    @23
    @37
    @2
    elin
    @40
    @20
    @26
    wa
    #
    @27
    wa
    @36
    @39
    @41
    @27
    vw
    vu
    vt
    cA
    vg
    vh
    dfac5lem.1
    dfac5lem2
    anbi1i
    @20
    @26
    @27
    anass
    bitri
    3bitri
    #
    eubii
    @20
    @28
    vg
    euanv
    bitr2i
    syl6ib
    @24
    vg
    wex
    @25
    @17
    @24
    vg
    euex
    @24
    @25
    @17
    wi
    #
    vg
    @25
    @17
    vg
    @24
    vg
    nfeu1
    @17
    vg
    nfv
    nfim
    @26
    @24
    @43
    @24
    @26
    @27
    @24
    @20
    @28
    @42
    simprbi
    simpld
    @26
    @24
    @25
    @17
    @24
    @25
    wa
    #
    @17
    @26
    @44
    @16
    @22
    @7
    vg
    @7
    cB
    tz6.12
    eleq1d
    biimparc
    exp32
    mpcom
    exlimi
    mpcom
    syl6
    expcomd
    ralrimiv
    @14
    @19
    vf
    cB
    cB
    @38
    cvv
    dfac5lem.2
    @2
    @37
    vy
    vex
    inex2
    eqeltri
    @9
    cB
    wceq
    #
    @12
    @18
    vw
    @13
    @45
    @11
    @17
    @8
    @45
    @10
    @16
    @7
    @7
    @9
    cB
    fveq1
    eleq1d
    imbi2d
    ralbidv
    spcev
    syl
    exlimiv
    syl
end
