include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cxr.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cv.mm"
include "cle.mm"
include "cif.mm"
include "cmpt.mm"
include "ccom.mm"
include "cmpt2.mm"
include "wa.mm"
include "simp1.mm"
include "xmetcl.mm"
include "xmetge0.mm"
include "elxrge0.mm"
include "sylanbrc.mm"
include "3expb.mm"
include "sylan.mm"
include "cxp.mm"
include "wfn.mm"
include "wceq.mm"
include "wf.mm"
include "xmetf.mm"
include "3ad2ant1.mm"
include "ffn.mm"
include "syl.mm"
include "fnov.mm"
include "sylib.mm"
include "eqidd.mm"
include "breq1.mm"
include "id.mm"
include "ifbieq1d.mm"
include "fmpt2co.mm"
include "syl6eqr.mm"
include "simplbi.mm"
include "simp2.mm"
include "ifcl.mm"
include "syl2anr.mm"
include "eqid.mm"
include "fmptd.mm"
include "cvv.mm"
include "vex.mm"
include "ifexg.mm"
include "sylancr.mm"
include "fvmptg.mm"
include "eqeq1d.mm"
include "wb.mm"
include "eqeq1.mm"
include "bibi1d.mm"
include "biidd.mm"
include "wn.mm"
include "simp3.mm"
include "gt0ne0d.mm"
include "neneqd.mm"
include "ad2antrr.mm"
include "wi.mm"
include "0xr.mm"
include "xrltle.mm"
include "mpd.mm"
include "adantr.mm"
include "syl5ibrcom.mm"
include "con3dimp.mm"
include "2falsed.mm"
include "ifbothda.mm"
include "bitrd.mm"
include "ad2antrl.mm"
include "xrmin1.mm"
include "syl2anc.mm"
include "ifcld.mm"
include "ad2antll.mm"
include "xrletr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "xrmin2.mm"
include "jctird.mm"
include "xrlemin.mm"
include "sylibrd.mm"
include "adantrr.mm"
include "simpr.mm"
include "breq12d.mm"
include "cxad.mm"
include "xaddcld.mm"
include "xaddid2.mm"
include "a1i.mm"
include "simprbi.mm"
include "xleadd1a.mm"
include "syl31anc.mm"
include "eqbrtrrd.mm"
include "xrletrd.mm"
include "oveq2.mm"
include "breq2d.mm"
include "ifboth.mm"
include "xaddid1.mm"
include "breq2.mm"
include "xleadd2a.mm"
include "oveq1.mm"
include "ge0xaddcl.mm"
include "ovex.mm"
include "oveq12d.mm"
include "3brtr4d.mm"
include "comet.mm"
include "eqeltrrd.mm"

theorem stdbdxmet
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cD: class D
  let cR: class R
  let cX: class X
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let vr: setvar r
  let vs: setvar s
  let vz: setvar z
  let cJ: class J
  let cS: class S
  let cB: class B
  let cP: class P
  assume stdbdmet.1: |- D = ( x e. X , y e. X |-> if ( ( x C y ) <_ R , ( x C y ) , R ) )

  disjoint x y
  disjoint C x
  disjoint C y
  disjoint R x
  disjoint R y
  disjoint X x
  disjoint X y
  disjoint A x
  disjoint A y
  disjoint a b
  disjoint a r
  disjoint a s
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint C a
  disjoint b r
  disjoint b s
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint C b
  disjoint r s
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint C r
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint C s
  disjoint x z
  disjoint y z
  disjoint C z
  disjoint D r
  disjoint D s
  disjoint D z
  disjoint J r
  disjoint J s
  disjoint J z
  disjoint S z
  disjoint B x
  disjoint B y
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint R a
  disjoint R b
  disjoint R r
  disjoint R s
  disjoint R z
  disjoint X a
  disjoint X b
  disjoint X r
  disjoint X s
  disjoint X z
  assert |- ( ( C e. ( *Met ` X ) /\ R e. RR* /\ 0 < R ) -> D e. ( *Met ` X ) )

  proof
    cC
    cX
    cxmt
    cfv
    #
    wcel
    #
    cR
    cxr
    wcel
    #
    cc0
    cR
    clt
    wbr
    #
    w3a
    #
    vz
    cc0
    cpnf
    cicc
    co
    #
    vz
    cv
    #
    cR
    cle
    wbr
    #
    @6
    cR
    cif
    #
    cmpt
    #
    cC
    ccom
    #
    cD
    @0
    @4
    @10
    vx
    vy
    cX
    cX
    vx
    cv
    #
    vy
    cv
    #
    cC
    co
    #
    cR
    cle
    wbr
    #
    @13
    cR
    cif
    #
    cmpt2
    cD
    @4
    vx
    vy
    vz
    cX
    cX
    @5
    @13
    @8
    @15
    cC
    @9
    @4
    @1
    @11
    cX
    wcel
    #
    @12
    cX
    wcel
    #
    wa
    @13
    @5
    wcel
    #
    @1
    @2
    @3
    simp1
    #
    @1
    @16
    @17
    @18
    @1
    @16
    @17
    w3a
    @13
    cxr
    wcel
    cc0
    @13
    cle
    wbr
    @18
    @11
    @12
    cC
    cX
    xmetcl
    @11
    @12
    cC
    cX
    xmetge0
    @13
    elxrge0
    sylanbrc
    3expb
    sylan
    @4
    cC
    cX
    cX
    cxp
    #
    wfn
    #
    cC
    vx
    vy
    cX
    cX
    @13
    cmpt2
    wceq
    @4
    @20
    cxr
    cC
    wf
    #
    @21
    @1
    @2
    @22
    @3
    cC
    cX
    xmetf
    3ad2ant1
    @20
    cxr
    cC
    ffn
    syl
    vx
    vy
    cX
    cX
    cC
    fnov
    sylib
    @4
    @9
    eqidd
    @6
    @13
    wceq
    #
    @7
    @14
    @6
    @13
    cR
    @6
    @13
    cR
    cle
    breq1
    @23
    id
    ifbieq1d
    fmpt2co
    stdbdmet.1
    syl6eqr
    @4
    va
    vb
    cC
    @9
    cX
    @19
    @4
    vz
    @5
    @8
    cxr
    @9
    @6
    @5
    wcel
    #
    @6
    cxr
    wcel
    #
    @2
    @8
    cxr
    wcel
    @4
    @24
    @25
    cc0
    @6
    cle
    wbr
    @6
    elxrge0
    simplbi
    @1
    @2
    @3
    simp2
    #
    @7
    @6
    cR
    cxr
    ifcl
    syl2anr
    @9
    eqid
    #
    fmptd
    @4
    va
    cv
    #
    @5
    wcel
    #
    wa
    #
    @28
    @9
    cfv
    #
    cc0
    wceq
    @28
    cR
    cle
    wbr
    #
    @28
    cR
    cif
    #
    cc0
    wceq
    #
    @28
    cc0
    wceq
    #
    @30
    @31
    @33
    cc0
    @29
    @29
    @33
    cvv
    wcel
    #
    @31
    @33
    wceq
    #
    @4
    @29
    id
    @4
    @28
    cvv
    wcel
    @2
    @36
    va
    vex
    @26
    @32
    @28
    cR
    cvv
    cxr
    ifexg
    sylancr
    vz
    @28
    @8
    @33
    @5
    cvv
    @9
    @6
    @28
    wceq
    #
    @7
    @32
    @6
    @28
    cR
    @6
    @28
    cR
    cle
    breq1
    @38
    id
    ifbieq1d
    @27
    fvmptg
    syl2anr
    #
    eqeq1d
    @32
    @35
    @35
    wb
    cR
    cc0
    wceq
    #
    @35
    wb
    @34
    @35
    wb
    @30
    @28
    cR
    @28
    @33
    wceq
    #
    @35
    @34
    @35
    @28
    @33
    cc0
    eqeq1
    bibi1d
    cR
    @33
    wceq
    #
    @40
    @34
    @35
    cR
    @33
    cc0
    eqeq1
    bibi1d
    @30
    @32
    wa
    @35
    biidd
    @30
    @32
    wn
    #
    wa
    @40
    @35
    @4
    @40
    wn
    @29
    @43
    @4
    cR
    cc0
    @4
    cR
    @1
    @2
    @3
    simp3
    #
    gt0ne0d
    neneqd
    ad2antrr
    @30
    @35
    @32
    @30
    @32
    @35
    cc0
    cR
    cle
    wbr
    #
    @4
    @45
    @29
    @4
    @3
    @45
    @44
    @4
    cc0
    cxr
    wcel
    #
    @2
    @3
    @45
    wi
    0xr
    @26
    cc0
    cR
    xrltle
    sylancr
    mpd
    #
    adantr
    @28
    cc0
    cR
    cle
    breq1
    syl5ibrcom
    con3dimp
    2falsed
    ifbothda
    bitrd
    @4
    @29
    vb
    cv
    #
    @5
    wcel
    #
    wa
    #
    wa
    #
    @28
    @48
    cle
    wbr
    #
    @33
    @48
    cR
    cle
    wbr
    #
    @48
    cR
    cif
    #
    cle
    wbr
    #
    @31
    @48
    @9
    cfv
    #
    cle
    wbr
    @51
    @52
    @33
    @48
    cle
    wbr
    #
    @33
    cR
    cle
    wbr
    #
    wa
    #
    @55
    @51
    @52
    @57
    @58
    @51
    @33
    @28
    cle
    wbr
    #
    @52
    @57
    @51
    @28
    cxr
    wcel
    #
    @2
    @60
    @29
    @61
    @4
    @49
    @29
    @61
    cc0
    @28
    cle
    wbr
    #
    @28
    elxrge0
    #
    simplbi
    ad2antrl
    #
    @4
    @2
    @50
    @26
    adantr
    #
    @28
    cR
    xrmin1
    syl2anc
    @51
    @33
    cxr
    wcel
    #
    @61
    @48
    cxr
    wcel
    #
    @60
    @52
    wa
    @57
    wi
    @51
    @32
    @28
    cR
    cxr
    @64
    @65
    ifcld
    #
    @64
    @49
    @67
    @4
    @29
    @49
    @67
    cc0
    @48
    cle
    wbr
    #
    @48
    elxrge0
    #
    simplbi
    ad2antll
    #
    @33
    @28
    @48
    xrletr
    syl3anc
    mpand
    @51
    @61
    @2
    @58
    @64
    @65
    @28
    cR
    xrmin2
    syl2anc
    jctird
    @51
    @66
    @67
    @2
    @55
    @59
    wb
    @68
    @71
    @65
    @33
    @48
    cR
    xrlemin
    syl3anc
    sylibrd
    @51
    @31
    @33
    @56
    @54
    cle
    @4
    @29
    @37
    @49
    @39
    adantrr
    #
    @50
    @49
    @54
    cvv
    wcel
    #
    @56
    @54
    wceq
    @4
    @29
    @49
    simpr
    @4
    @48
    cvv
    wcel
    @2
    @73
    vb
    vex
    @26
    @53
    @48
    cR
    cvv
    cxr
    ifexg
    sylancr
    vz
    @48
    @8
    @54
    @5
    cvv
    @9
    @6
    @48
    wceq
    #
    @7
    @53
    @6
    @48
    cR
    @6
    @48
    cR
    cle
    breq1
    @74
    id
    ifbieq1d
    @27
    fvmptg
    syl2anr
    #
    breq12d
    sylibrd
    @51
    @28
    @48
    cxad
    co
    #
    cR
    cle
    wbr
    #
    @76
    cR
    cif
    #
    @33
    @54
    cxad
    co
    #
    @76
    @9
    cfv
    #
    @31
    @56
    cxad
    co
    cle
    @51
    @78
    @28
    @54
    cxad
    co
    #
    cle
    wbr
    #
    @78
    cR
    @54
    cxad
    co
    #
    cle
    wbr
    #
    @78
    @79
    cle
    wbr
    #
    @51
    @78
    @76
    cle
    wbr
    #
    @78
    @28
    cR
    cxad
    co
    #
    cle
    wbr
    #
    @82
    @51
    @76
    cxr
    wcel
    #
    @2
    @86
    @51
    @28
    @48
    @64
    @71
    xaddcld
    #
    @65
    @76
    cR
    xrmin1
    syl2anc
    @51
    @78
    cR
    @87
    @51
    @77
    @76
    cR
    cxr
    @90
    @65
    ifcld
    #
    @65
    @51
    @28
    cR
    @64
    @65
    xaddcld
    @51
    @89
    @2
    @78
    cR
    cle
    wbr
    @90
    @65
    @76
    cR
    xrmin2
    syl2anc
    #
    @51
    cc0
    cR
    cxad
    co
    #
    cR
    @87
    cle
    @51
    @2
    @93
    cR
    wceq
    @65
    cR
    xaddid2
    syl
    @51
    @46
    @61
    @2
    @62
    @93
    @87
    cle
    wbr
    @46
    @51
    0xr
    a1i
    #
    @64
    @65
    @29
    @62
    @4
    @49
    @29
    @61
    @62
    @63
    simprbi
    ad2antrl
    cc0
    @28
    cR
    xleadd1a
    syl31anc
    eqbrtrrd
    xrletrd
    @53
    @86
    @88
    @82
    @48
    cR
    @48
    @54
    wceq
    @76
    @81
    @78
    cle
    @48
    @54
    @28
    cxad
    oveq2
    breq2d
    cR
    @54
    wceq
    @87
    @81
    @78
    cle
    cR
    @54
    @28
    cxad
    oveq2
    breq2d
    ifboth
    syl2anc
    @51
    @78
    cR
    @83
    @91
    @65
    @51
    cR
    @54
    @65
    @51
    @53
    @48
    cR
    cxr
    @71
    @65
    ifcld
    #
    xaddcld
    @92
    @51
    cR
    cc0
    cxad
    co
    #
    cR
    @83
    cle
    @51
    @2
    @96
    cR
    wceq
    @65
    cR
    xaddid1
    syl
    @51
    @46
    @54
    cxr
    wcel
    @2
    cc0
    @54
    cle
    wbr
    #
    @96
    @83
    cle
    wbr
    @94
    @95
    @65
    @51
    @69
    @45
    @97
    @49
    @69
    @4
    @29
    @49
    @67
    @69
    @70
    simprbi
    ad2antll
    @4
    @45
    @50
    @47
    adantr
    @53
    @69
    @45
    @97
    @48
    cR
    @48
    @54
    cc0
    cle
    breq2
    cR
    @54
    cc0
    cle
    breq2
    ifboth
    syl2anc
    cc0
    @54
    cR
    xleadd2a
    syl31anc
    eqbrtrrd
    xrletrd
    @32
    @82
    @84
    @85
    @28
    cR
    @41
    @81
    @79
    @78
    cle
    @28
    @33
    @54
    cxad
    oveq1
    breq2d
    @42
    @83
    @79
    @78
    cle
    cR
    @33
    @54
    cxad
    oveq1
    breq2d
    ifboth
    syl2anc
    @50
    @76
    @5
    wcel
    @78
    cvv
    wcel
    #
    @80
    @78
    wceq
    @4
    @28
    @48
    ge0xaddcl
    @4
    @76
    cvv
    wcel
    @2
    @98
    @28
    @48
    cxad
    ovex
    @26
    @77
    @76
    cR
    cvv
    cxr
    ifexg
    sylancr
    vz
    @76
    @8
    @78
    @5
    cvv
    @9
    @6
    @76
    wceq
    #
    @7
    @77
    @6
    @76
    cR
    @6
    @76
    cR
    cle
    breq1
    @99
    id
    ifbieq1d
    @27
    fvmptg
    syl2anr
    @51
    @31
    @33
    @56
    @54
    cxad
    @72
    @75
    oveq12d
    3brtr4d
    comet
    eqeltrrd
end
