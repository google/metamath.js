include "cmnd.mm"
include "wcel.mm"
include "csubmnd.mm"
include "cfv.mm"
include "c0g.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wral.mm"
include "wa.mm"
include "cbs.mm"
include "cpw.mm"
include "crab.mm"
include "wss.mm"
include "w3a.mm"
include "wceq.mm"
include "fveq2.mm"
include "pweqd.mm"
include "eleq1d.mm"
include "oveqd.mm"
include "2ralbidv.mm"
include "anbi12d.mm"
include "rabeqbidv.mm"
include "df-submnd.mm"
include "fvex.mm"
include "pwex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "eleq2d.mm"
include "eleq2.mm"
include "raleqbi1dv.mm"
include "elrab.mm"
include "sseq2i.mm"
include "eleq1i.mm"
include "oveqi.mm"
include "2ralbii.mm"
include "anbi12i.mm"
include "3anass.mm"
include "elpw2.mm"
include "anbi1i.mm"
include "3bitr4ri.mm"
include "bitri.mm"
include "syl6bb.mm"

theorem issubm
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let cM: class M
  let c.0: class .0.
  let vm: setvar m
  let vt: setvar t
  let vs: setvar s
  assume issubm.b: |- B = ( Base ` M )
  assume issubm.z: |- .0. = ( 0g ` M )
  assume issubm.p: |- .+ = ( +g ` M )

  disjoint M x
  disjoint M y
  disjoint x y
  disjoint S x
  disjoint S y
  disjoint M m
  disjoint M t
  disjoint m t
  disjoint m x
  disjoint m y
  disjoint t x
  disjoint t y
  disjoint S t
  disjoint s t
  disjoint s x
  disjoint s y
  assert |- ( M e. Mnd -> ( S e. ( SubMnd ` M ) <-> ( S C_ B /\ .0. e. S /\ A. x e. S A. y e. S ( x .+ y ) e. S ) ) )

  proof
    cM
    cmnd
    wcel
    #
    cS
    cM
    csubmnd
    cfv
    #
    wcel
    cS
    cM
    c0g
    cfv
    #
    vt
    cv
    #
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cM
    cplusg
    cfv
    #
    co
    #
    @3
    wcel
    #
    vy
    @3
    wral
    #
    vx
    @3
    wral
    #
    wa
    #
    vt
    cM
    cbs
    cfv
    #
    cpw
    #
    crab
    #
    wcel
    #
    cS
    cB
    wss
    #
    c.0
    cS
    wcel
    #
    @5
    @6
    c.pl
    co
    #
    cS
    wcel
    #
    vy
    cS
    wral
    vx
    cS
    wral
    #
    w3a
    #
    @0
    @1
    @15
    cS
    vm
    cM
    vm
    cv
    #
    c0g
    cfv
    #
    @3
    wcel
    #
    @5
    @6
    @23
    cplusg
    cfv
    #
    co
    #
    @3
    wcel
    #
    vy
    @3
    wral
    vx
    @3
    wral
    #
    wa
    #
    vt
    @23
    cbs
    cfv
    #
    cpw
    #
    crab
    @15
    cmnd
    csubmnd
    @23
    cM
    wceq
    #
    @30
    @12
    vt
    @32
    @14
    @33
    @31
    @13
    @23
    cM
    cbs
    fveq2
    pweqd
    @33
    @25
    @4
    @29
    @11
    @33
    @24
    @2
    @3
    @23
    cM
    c0g
    fveq2
    eleq1d
    @33
    @28
    @9
    vx
    vy
    @3
    @3
    @33
    @27
    @8
    @3
    @33
    @26
    @7
    @5
    @6
    @23
    cM
    cplusg
    fveq2
    oveqd
    eleq1d
    2ralbidv
    anbi12d
    rabeqbidv
    vx
    vy
    vt
    vm
    df-submnd
    @12
    vt
    @14
    @13
    cM
    cbs
    fvex
    #
    pwex
    rabex
    fvmpt
    eleq2d
    @16
    cS
    @14
    wcel
    #
    @2
    cS
    wcel
    #
    @8
    cS
    wcel
    #
    vy
    cS
    wral
    #
    vx
    cS
    wral
    #
    wa
    #
    wa
    #
    @22
    @12
    @40
    vt
    cS
    @14
    @3
    cS
    wceq
    @4
    @36
    @11
    @39
    @3
    cS
    @2
    eleq2
    @10
    @38
    vx
    @3
    cS
    @9
    @37
    vy
    @3
    cS
    @3
    cS
    @8
    eleq2
    raleqbi1dv
    raleqbi1dv
    anbi12d
    elrab
    @17
    @18
    @21
    wa
    #
    wa
    cS
    @13
    wss
    #
    @40
    wa
    @22
    @41
    @17
    @43
    @42
    @40
    cB
    @13
    cS
    issubm.b
    sseq2i
    @18
    @36
    @21
    @39
    c.0
    @2
    cS
    issubm.z
    eleq1i
    @20
    @37
    vx
    vy
    cS
    cS
    @19
    @8
    cS
    c.pl
    @7
    @5
    @6
    issubm.p
    oveqi
    eleq1i
    2ralbii
    anbi12i
    anbi12i
    @17
    @18
    @21
    3anass
    @35
    @43
    @40
    cS
    @13
    @34
    elpw2
    anbi1i
    3bitr4ri
    bitri
    syl6bb
end
