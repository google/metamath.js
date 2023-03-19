include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "cdif.mm"
include "csdm.mm"
include "cpw.mm"
include "crab.mm"
include "wss.mm"
include "wb.mm"
include "wceq.mm"
include "difeq2.mm"
include "breq1d.mm"
include "elrab.mm"
include "selpw.mm"
include "anbi1i.mm"
include "bitri.mm"
include "a1i.mm"
include "cvv.mm"
include "elex.mm"
include "adantr.mm"
include "wsbc.mm"
include "c0.mm"
include "difid.mm"
include "wne.mm"
include "infn0.mm"
include "adantl.mm"
include "0sdomg.mm"
include "mpbird.mm"
include "syl5eqbr.mm"
include "sbcieg.mm"
include "sdomirr.mm"
include "0ex.mm"
include "dif0.mm"
include "syl6eq.mm"
include "sbcie.mm"
include "mtbiri.mm"
include "w3a.mm"
include "wi.mm"
include "simp1l.mm"
include "difexg.mm"
include "syl.mm"
include "sscon.mm"
include "3ad2ant3.mm"
include "ssdomg.mm"
include "sylc.mm"
include "domsdomtr.mm"
include "ex.mm"
include "vex.mm"
include "3imtr4g.mm"
include "cin.mm"
include "cun.mm"
include "infunsdom.mm"
include "difindi.mm"
include "breq1i.mm"
include "syl6ibr.mm"
include "3ad2ant1.mm"
include "anbi12i.mm"
include "inex1.mm"
include "isfild.mm"

theorem csdfil
  let vx: setvar x
  let cX: class X
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z

  disjoint X x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint X w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint X y
  disjoint X z
  assert |- ( ( X e. dom card /\ _om ~<_ X ) -> { x e. ~P X | ( X \ x ) ~< X } e. ( Fil ` X ) )

  proof
    cX
    ccrd
    cdm
    #
    wcel
    #
    com
    cX
    cdom
    wbr
    #
    wa
    #
    cX
    vy
    cv
    #
    cdif
    #
    cX
    csdm
    wbr
    #
    vy
    vz
    vw
    cX
    cX
    vx
    cv
    #
    cdif
    #
    cX
    csdm
    wbr
    #
    vx
    cX
    cpw
    #
    crab
    #
    @4
    @11
    wcel
    #
    @4
    cX
    wss
    #
    @6
    wa
    #
    wb
    @3
    @12
    @4
    @10
    wcel
    #
    @6
    wa
    @14
    @9
    @6
    vx
    @4
    @10
    @7
    @4
    wceq
    @8
    @5
    cX
    csdm
    @7
    @4
    cX
    difeq2
    breq1d
    elrab
    @15
    @13
    @6
    vy
    cX
    selpw
    anbi1i
    bitri
    a1i
    @1
    cX
    cvv
    wcel
    @2
    cX
    @0
    elex
    adantr
    @3
    @6
    vy
    cX
    wsbc
    #
    cX
    cX
    cdif
    #
    cX
    csdm
    wbr
    #
    @3
    @17
    c0
    cX
    csdm
    cX
    difid
    @3
    c0
    cX
    csdm
    wbr
    #
    cX
    c0
    wne
    #
    @2
    @20
    @1
    cX
    infn0
    adantl
    @1
    @19
    @20
    wb
    @2
    cX
    @0
    0sdomg
    adantr
    mpbird
    syl5eqbr
    @1
    @16
    @18
    wb
    @2
    @6
    @18
    vy
    cX
    @0
    @4
    cX
    wceq
    @5
    @17
    cX
    csdm
    @4
    cX
    cX
    difeq2
    breq1d
    sbcieg
    adantr
    mpbird
    @3
    @6
    vy
    c0
    wsbc
    #
    cX
    cX
    csdm
    wbr
    #
    cX
    sdomirr
    @21
    @22
    wb
    @3
    @6
    @22
    vy
    c0
    0ex
    @4
    c0
    wceq
    #
    @5
    cX
    cX
    csdm
    @23
    @5
    cX
    c0
    cdif
    cX
    @4
    c0
    cX
    difeq2
    cX
    dif0
    syl6eq
    breq1d
    sbcie
    a1i
    mtbiri
    @3
    vz
    cv
    #
    cX
    wss
    #
    vw
    cv
    #
    @24
    wss
    #
    w3a
    #
    cX
    @26
    cdif
    #
    cX
    csdm
    wbr
    #
    cX
    @24
    cdif
    #
    cX
    csdm
    wbr
    #
    @6
    vy
    @26
    wsbc
    #
    @6
    vy
    @24
    wsbc
    #
    @28
    @31
    @29
    cdom
    wbr
    #
    @30
    @32
    wi
    @28
    @29
    cvv
    wcel
    #
    @31
    @29
    wss
    #
    @35
    @28
    @1
    @36
    @1
    @2
    @25
    @27
    simp1l
    cX
    @26
    @0
    difexg
    syl
    @27
    @3
    @37
    @25
    @26
    @24
    cX
    sscon
    3ad2ant3
    @31
    @29
    cvv
    ssdomg
    sylc
    @35
    @30
    @32
    @31
    @29
    cX
    domsdomtr
    ex
    syl
    @6
    @30
    vy
    @26
    vw
    vex
    @4
    @26
    wceq
    @5
    @29
    cX
    csdm
    @4
    @26
    cX
    difeq2
    breq1d
    sbcie
    #
    @6
    @32
    vy
    @24
    vz
    vex
    #
    @4
    @24
    wceq
    @5
    @31
    cX
    csdm
    @4
    @24
    cX
    difeq2
    breq1d
    sbcie
    #
    3imtr4g
    @3
    @25
    @26
    cX
    wss
    #
    w3a
    @32
    @30
    wa
    #
    cX
    @24
    @26
    cin
    #
    cdif
    #
    cX
    csdm
    wbr
    #
    @34
    @33
    wa
    @6
    vy
    @43
    wsbc
    @3
    @25
    @42
    @45
    wi
    @41
    @3
    @42
    @31
    @29
    cun
    #
    cX
    csdm
    wbr
    #
    @45
    @3
    @42
    @47
    @31
    @29
    cX
    infunsdom
    ex
    @44
    @46
    cX
    csdm
    cX
    @24
    @26
    difindi
    breq1i
    syl6ibr
    3ad2ant1
    @34
    @32
    @33
    @30
    @40
    @38
    anbi12i
    @6
    @45
    vy
    @43
    @24
    @26
    @39
    inex1
    @4
    @43
    wceq
    @5
    @44
    cX
    csdm
    @4
    @43
    cX
    difeq2
    breq1d
    sbcie
    3imtr4g
    isfild
end
