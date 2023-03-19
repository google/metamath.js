include "ctsr.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wne.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cordt.mm"
include "cfv.mm"
include "wrex.mm"
include "wa.mm"
include "wn.mm"
include "crab.mm"
include "simpll1.mm"
include "simpll3.mm"
include "ordtopn2.mm"
include "syl2anc.mm"
include "simpll2.mm"
include "ordtopn1.mm"
include "simprr.mm"
include "cps.mm"
include "wi.mm"
include "simpl1.mm"
include "tsrps.mm"
include "syl.mm"
include "simprl.mm"
include "psasym.mm"
include "3expia.mm"
include "necon3ad.mm"
include "mpd.mm"
include "adantr.mm"
include "breq2.mm"
include "notbid.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "breq1.mm"
include "simpr.mm"
include "eleq2.mm"
include "ineq1.mm"
include "eqeq1d.mm"
include "3anbi13d.mm"
include "ineq2.mm"
include "inrab.mm"
include "syl6eq.mm"
include "3anbi23d.mm"
include "rspc2ev.mm"
include "syl113anc.mm"
include "ex.mm"
include "rabn0.mm"
include "simprrr.mm"
include "simprrl.mm"
include "wral.mm"
include "wo.mm"
include "jca.mm"
include "tsrlin.mm"
include "3expa.mm"
include "sylan.mm"
include "oran.mm"
include "sylib.mm"
include "ralrimiva.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "rexlimdvaa.mm"
include "syl5bi.mm"
include "pm2.61dne.mm"
include "exp32.mm"

theorem ordthauslem
  let cA: class A
  let cB: class B
  let cR: class R
  let vm: setvar m
  let vn: setvar n
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume ordthauslem.1: |- X = dom R

  disjoint m n
  disjoint A m
  disjoint A n
  disjoint B m
  disjoint B n
  disjoint R m
  disjoint R n
  disjoint X m
  disjoint X n
  disjoint m x
  disjoint m y
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint R x
  disjoint R y
  disjoint X x
  disjoint X y
  assert |- ( ( R e. TosetRel /\ A e. X /\ B e. X ) -> ( A R B -> ( A =/= B -> E. m e. ( ordTop ` R ) E. n e. ( ordTop ` R ) ( A e. m /\ B e. n /\ ( m i^i n ) = (/) ) ) ) )

  proof
    cR
    ctsr
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    cA
    cB
    cR
    wbr
    #
    cA
    cB
    wne
    #
    cA
    vm
    cv
    #
    wcel
    #
    cB
    vn
    cv
    #
    wcel
    #
    @6
    @8
    cin
    #
    c0
    wceq
    #
    w3a
    #
    vn
    cR
    cordt
    cfv
    #
    wrex
    vm
    @13
    wrex
    #
    @3
    @4
    @5
    wa
    #
    wa
    #
    @14
    cB
    vx
    cv
    #
    cR
    wbr
    #
    wn
    #
    @17
    cA
    cR
    wbr
    #
    wn
    #
    wa
    #
    vx
    cX
    crab
    #
    c0
    @16
    @23
    c0
    wceq
    #
    @14
    @16
    @24
    wa
    #
    @19
    vx
    cX
    crab
    #
    @13
    wcel
    #
    @21
    vx
    cX
    crab
    #
    @13
    wcel
    #
    cA
    @26
    wcel
    #
    cB
    @28
    wcel
    #
    @24
    @14
    @25
    @0
    @2
    @27
    @0
    @1
    @2
    @15
    @24
    simpll1
    #
    @0
    @1
    @2
    @15
    @24
    simpll3
    #
    vx
    cB
    cR
    ctsr
    cX
    ordthauslem.1
    ordtopn2
    syl2anc
    @25
    @0
    @1
    @29
    @32
    @0
    @1
    @2
    @15
    @24
    simpll2
    #
    vx
    cA
    cR
    ctsr
    cX
    ordthauslem.1
    ordtopn1
    syl2anc
    @25
    @1
    cB
    cA
    cR
    wbr
    #
    wn
    #
    @30
    @34
    @16
    @36
    @24
    @16
    @5
    @36
    @3
    @4
    @5
    simprr
    @16
    @35
    cA
    cB
    @16
    cR
    cps
    wcel
    #
    @4
    @35
    cA
    cB
    wceq
    #
    wi
    @16
    @0
    @37
    @0
    @1
    @2
    @15
    simpl1
    cR
    tsrps
    syl
    @3
    @4
    @5
    simprl
    @37
    @4
    @35
    @38
    cA
    cB
    cR
    psasym
    3expia
    syl2anc
    necon3ad
    mpd
    adantr
    #
    @19
    @36
    vx
    cA
    cX
    @17
    cA
    wceq
    @18
    @35
    @17
    cA
    cB
    cR
    breq2
    notbid
    elrab
    sylanbrc
    @25
    @2
    @36
    @31
    @33
    @39
    @21
    @36
    vx
    cB
    cX
    @17
    cB
    wceq
    @20
    @35
    @17
    cB
    cA
    cR
    breq1
    notbid
    elrab
    sylanbrc
    @16
    @24
    simpr
    @12
    @30
    @31
    @24
    w3a
    @30
    @9
    @26
    @8
    cin
    #
    c0
    wceq
    #
    w3a
    vm
    vn
    @26
    @28
    @13
    @13
    @6
    @26
    wceq
    #
    @7
    @30
    @11
    @41
    @9
    @6
    @26
    cA
    eleq2
    @42
    @10
    @40
    c0
    @6
    @26
    @8
    ineq1
    eqeq1d
    3anbi13d
    @8
    @28
    wceq
    #
    @9
    @31
    @41
    @24
    @30
    @8
    @28
    cB
    eleq2
    @43
    @40
    @23
    c0
    @43
    @40
    @26
    @28
    cin
    @23
    @8
    @28
    @26
    ineq2
    @19
    @21
    vx
    cX
    inrab
    syl6eq
    eqeq1d
    3anbi23d
    rspc2ev
    syl113anc
    ex
    @23
    c0
    wne
    @22
    vx
    cX
    wrex
    @16
    @14
    @22
    vx
    cX
    rabn0
    @16
    @22
    @14
    vx
    cX
    @16
    @17
    cX
    wcel
    #
    @22
    wa
    #
    wa
    #
    @17
    vy
    cv
    #
    cR
    wbr
    #
    wn
    #
    vy
    cX
    crab
    #
    @13
    wcel
    #
    @47
    @17
    cR
    wbr
    #
    wn
    #
    vy
    cX
    crab
    #
    @13
    wcel
    #
    cA
    @50
    wcel
    #
    cB
    @54
    wcel
    #
    @49
    @53
    wa
    #
    vy
    cX
    crab
    #
    c0
    wceq
    #
    @14
    @46
    @0
    @44
    @51
    @0
    @1
    @2
    @15
    @45
    simpll1
    #
    @16
    @44
    @22
    simprl
    #
    vy
    @17
    cR
    ctsr
    cX
    ordthauslem.1
    ordtopn2
    syl2anc
    @46
    @0
    @44
    @55
    @61
    @62
    vy
    @17
    cR
    ctsr
    cX
    ordthauslem.1
    ordtopn1
    syl2anc
    @46
    @1
    @21
    @56
    @0
    @1
    @2
    @15
    @45
    simpll2
    @16
    @44
    @19
    @21
    simprrr
    @49
    @21
    vy
    cA
    cX
    @47
    cA
    wceq
    @48
    @20
    @47
    cA
    @17
    cR
    breq2
    notbid
    elrab
    sylanbrc
    @46
    @2
    @19
    @57
    @0
    @1
    @2
    @15
    @45
    simpll3
    @16
    @44
    @19
    @21
    simprrl
    @53
    @19
    vy
    cB
    cX
    @47
    cB
    wceq
    @52
    @18
    @47
    cB
    @17
    cR
    breq1
    notbid
    elrab
    sylanbrc
    @46
    @58
    wn
    #
    vy
    cX
    wral
    @60
    @46
    @63
    vy
    cX
    @46
    @47
    cX
    wcel
    #
    wa
    @48
    @52
    wo
    #
    @63
    @46
    @0
    @44
    wa
    @64
    @65
    @46
    @0
    @44
    @61
    @62
    jca
    @0
    @44
    @64
    @65
    @17
    @47
    cR
    cX
    ordthauslem.1
    tsrlin
    3expa
    sylan
    @48
    @52
    oran
    sylib
    ralrimiva
    @58
    vy
    cX
    rabeq0
    sylibr
    @12
    @56
    @57
    @60
    w3a
    @56
    @9
    @50
    @8
    cin
    #
    c0
    wceq
    #
    w3a
    vm
    vn
    @50
    @54
    @13
    @13
    @6
    @50
    wceq
    #
    @7
    @56
    @11
    @67
    @9
    @6
    @50
    cA
    eleq2
    @68
    @10
    @66
    c0
    @6
    @50
    @8
    ineq1
    eqeq1d
    3anbi13d
    @8
    @54
    wceq
    #
    @9
    @57
    @67
    @60
    @56
    @8
    @54
    cB
    eleq2
    @69
    @66
    @59
    c0
    @69
    @66
    @50
    @54
    cin
    @59
    @8
    @54
    @50
    ineq2
    @49
    @53
    vy
    cX
    inrab
    syl6eq
    eqeq1d
    3anbi23d
    rspc2ev
    syl113anc
    rexlimdvaa
    syl5bi
    pm2.61dne
    exp32
end
