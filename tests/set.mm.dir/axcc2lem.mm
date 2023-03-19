include "cv.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "wcel.mm"
include "wi.mm"
include "crn.mm"
include "wral.mm"
include "com.mm"
include "wfn.mm"
include "wa.mm"
include "wex.mm"
include "c2nd.mm"
include "fvex.mm"
include "fnmpti.mm"
include "w3a.mm"
include "csn.mm"
include "cxp.mm"
include "cvv.mm"
include "wceq.mm"
include "snex.mm"
include "xpex.mm"
include "fvmpt2.mm"
include "mpan2.mm"
include "vex.mm"
include "snnz.mm"
include "cif.mm"
include "0ex.mm"
include "iftrue.mm"
include "neeq1d.mm"
include "mpbiri.mm"
include "wn.mm"
include "iffalse.mm"
include "df-ne.mm"
include "biimpri.mm"
include "eqnetrd.mm"
include "pm2.61i.mm"
include "p0ex.mm"
include "ifex.mm"
include "xpnz.mm"
include "biimpi.mm"
include "sylancr.mm"
include "fnfvelrn.mm"
include "mpan.mm"
include "neeq1.mm"
include "fveq2.mm"
include "id.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "rspccv.mm"
include "syl5.mm"
include "mpdi.mm"
include "impcom.mm"
include "wb.mm"
include "eleq2d.mm"
include "adantr.mm"
include "mpbid.mm"
include "xp2nd.mm"
include "syl.mm"
include "3adant3.mm"
include "3ad2ant1.mm"
include "eqcomd.mm"
include "ifnefalse.mm"
include "3ad2ant3.mm"
include "eqtrd.mm"
include "3eltr3d.mm"
include "3expia.mm"
include "expcom.mm"
include "ralrimiv.mm"
include "omex.mm"
include "fnex.mm"
include "mp2an.mm"
include "fneq1.mm"
include "fveq1.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "spcev.mm"
include "wf1.mm"
include "cen.mm"
include "wbr.mm"
include "wf.mm"
include "a1i.mm"
include "fmptd.mm"
include "ax-mp.mm"
include "sneq.mm"
include "xpeq12d.mm"
include "fvmpt3i.mm"
include "adantl.mm"
include "eqeq2d.mm"
include "eqeq1d.mm"
include "xp11.mm"
include "sneqr.mm"
include "syl6bi.mm"
include "sylbid.mm"
include "rgen2a.mm"
include "dff13.mm"
include "mpbir2an.mm"
include "wf1o.mm"
include "f1f1orn.mm"
include "f1oen.mm"
include "ensym.mm"
include "3syl.mm"
include "cmpt.mm"
include "rneqi.mm"
include "cdm.mm"
include "wfun.mm"
include "dmmptg.mm"
include "mprg.mm"
include "eqeltri.mm"
include "funmpt.mm"
include "funrnex.mm"
include "mp2.mm"
include "breq1.mm"
include "raleq.mm"
include "exbidv.mm"
include "ax-cc.mm"
include "vtocl.mm"
include "mp2b.mm"
include "exlimiiv.mm"

theorem axcc2lem
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cK: class K
  let va: setvar a
  let vz: setvar z
  let vk: setvar k
  assume axcc2lem.1: |- K = ( n e. _om |-> if ( ( F ` n ) = (/) , { (/) } , ( F ` n ) ) )
  assume axcc2lem.2: |- A = ( n e. _om |-> ( { n } X. ( K ` n ) ) )
  assume axcc2lem.3: |- G = ( n e. _om |-> ( 2nd ` ( f ` ( A ` n ) ) ) )

  disjoint A f
  disjoint A n
  disjoint f n
  disjoint F f
  disjoint F g
  disjoint f g
  disjoint G g
  disjoint G n
  disjoint g n
  disjoint K n
  disjoint A a
  disjoint A z
  disjoint a f
  disjoint a z
  disjoint f z
  disjoint A k
  disjoint k n
  disjoint n z
  assert |- E. g ( g Fn _om /\ A. n e. _om ( ( F ` n ) =/= (/) -> ( g ` n ) e. ( F ` n ) ) )

  proof
    vz
    cv
    #
    c0
    wne
    #
    @0
    vf
    cv
    #
    cfv
    #
    @0
    wcel
    #
    wi
    #
    vz
    cA
    crn
    #
    wral
    #
    vg
    cv
    #
    com
    wfn
    #
    vn
    cv
    #
    cF
    cfv
    #
    c0
    wne
    #
    @10
    @8
    cfv
    #
    @11
    wcel
    #
    wi
    #
    vn
    com
    wral
    #
    wa
    #
    vg
    wex
    #
    vf
    @7
    cG
    com
    wfn
    #
    @12
    @10
    cG
    cfv
    #
    @11
    wcel
    #
    wi
    #
    vn
    com
    wral
    #
    @18
    vn
    com
    @10
    cA
    cfv
    #
    @2
    cfv
    #
    c2nd
    cfv
    #
    cG
    @25
    c2nd
    fvex
    #
    axcc2lem.3
    fnmpti
    #
    @7
    @22
    vn
    com
    @10
    com
    wcel
    #
    @7
    @22
    @29
    @7
    @12
    @21
    @29
    @7
    @12
    w3a
    #
    @26
    @10
    cK
    cfv
    #
    @20
    @11
    @29
    @7
    @26
    @31
    wcel
    #
    @12
    @29
    @7
    wa
    #
    @25
    @10
    csn
    #
    @31
    cxp
    #
    wcel
    #
    @32
    @33
    @25
    @24
    wcel
    #
    @36
    @7
    @29
    @37
    @7
    @29
    @24
    c0
    wne
    #
    @37
    @29
    @24
    @35
    c0
    @29
    @35
    cvv
    wcel
    #
    @24
    @35
    wceq
    #
    @34
    @31
    @10
    snex
    @10
    cK
    fvex
    xpex
    #
    vn
    com
    @35
    cvv
    cA
    axcc2lem.2
    fvmpt2
    mpan2
    #
    @29
    @34
    c0
    wne
    #
    @31
    c0
    wne
    #
    @35
    c0
    wne
    #
    @10
    vn
    vex
    #
    snnz
    #
    @29
    @44
    @11
    c0
    wceq
    #
    c0
    csn
    #
    @11
    cif
    #
    c0
    wne
    #
    @48
    @51
    @48
    @51
    @49
    c0
    wne
    c0
    0ex
    snnz
    @48
    @50
    @49
    c0
    @48
    @49
    @11
    iftrue
    neeq1d
    mpbiri
    @48
    wn
    #
    @50
    @11
    c0
    @48
    @49
    @11
    iffalse
    @12
    @52
    @11
    c0
    df-ne
    biimpri
    eqnetrd
    pm2.61i
    @29
    @31
    @50
    c0
    @29
    @50
    cvv
    wcel
    @31
    @50
    wceq
    #
    @48
    @49
    @11
    p0ex
    @10
    cF
    fvex
    ifex
    vn
    com
    @50
    cvv
    cK
    axcc2lem.1
    fvmpt2
    mpan2
    #
    neeq1d
    mpbiri
    #
    @43
    @44
    wa
    @45
    @34
    @31
    xpnz
    biimpi
    sylancr
    eqnetrd
    @29
    @24
    @6
    wcel
    #
    @7
    @38
    @37
    wi
    #
    cA
    com
    wfn
    @29
    @56
    vn
    com
    @35
    cA
    @41
    axcc2lem.2
    fnmpti
    com
    @10
    cA
    fnfvelrn
    mpan
    @5
    @57
    vz
    @24
    @6
    @0
    @24
    wceq
    #
    @1
    @38
    @4
    @37
    @0
    @24
    c0
    neeq1
    @58
    @3
    @25
    @0
    @24
    @0
    @24
    @2
    fveq2
    @58
    id
    eleq12d
    imbi12d
    rspccv
    syl5
    mpdi
    impcom
    @29
    @37
    @36
    wb
    @7
    @29
    @24
    @35
    @25
    @42
    eleq2d
    adantr
    mpbid
    @25
    @34
    @31
    xp2nd
    syl
    3adant3
    @30
    @20
    @26
    @29
    @7
    @20
    @26
    wceq
    #
    @12
    @29
    @26
    cvv
    wcel
    @59
    @27
    vn
    com
    @26
    cvv
    cG
    axcc2lem.3
    fvmpt2
    mpan2
    3ad2ant1
    eqcomd
    @30
    @31
    @50
    @11
    @29
    @7
    @53
    @12
    @54
    3ad2ant1
    @12
    @29
    @50
    @11
    wceq
    @7
    @11
    c0
    @49
    @11
    ifnefalse
    3ad2ant3
    eqtrd
    3eltr3d
    3expia
    expcom
    ralrimiv
    @17
    @19
    @23
    wa
    vg
    cG
    @19
    com
    cvv
    wcel
    #
    cG
    cvv
    wcel
    @28
    omex
    com
    cvv
    cG
    fnex
    mp2an
    @8
    cG
    wceq
    #
    @9
    @19
    @16
    @23
    com
    @8
    cG
    fneq1
    @61
    @15
    @22
    vn
    com
    @61
    @14
    @21
    @12
    @61
    @13
    @20
    @11
    @10
    @8
    cG
    fveq1
    eleq1d
    imbi2d
    ralbidv
    anbi12d
    spcev
    sylancr
    com
    cvv
    cA
    wf1
    #
    @6
    com
    cen
    wbr
    #
    @7
    vf
    wex
    #
    @62
    com
    cvv
    cA
    wf
    #
    @24
    vk
    cv
    #
    cA
    cfv
    #
    wceq
    #
    @10
    @66
    wceq
    #
    wi
    #
    vk
    com
    wral
    vn
    com
    wral
    @60
    @65
    omex
    @60
    vn
    com
    @35
    cvv
    cA
    @39
    @60
    @29
    wa
    @41
    a1i
    axcc2lem.2
    fmptd
    ax-mp
    @70
    vn
    vk
    com
    @29
    @66
    com
    wcel
    #
    wa
    #
    @68
    @24
    @66
    csn
    #
    @66
    cK
    cfv
    #
    cxp
    #
    wceq
    #
    @69
    @72
    @67
    @75
    @24
    @71
    @67
    @75
    wceq
    @29
    vn
    @66
    @35
    @75
    com
    cA
    @69
    @34
    @73
    @31
    @74
    @10
    @66
    sneq
    @10
    @66
    cK
    fveq2
    xpeq12d
    axcc2lem.2
    @41
    fvmpt3i
    adantl
    eqeq2d
    @72
    @76
    @35
    @75
    wceq
    #
    @69
    @72
    @24
    @35
    @75
    @29
    @40
    @71
    @42
    adantr
    eqeq1d
    @29
    @77
    @69
    wi
    @71
    @29
    @77
    @34
    @73
    wceq
    #
    @31
    @74
    wceq
    #
    wa
    #
    @69
    @29
    @43
    @44
    @77
    @80
    wb
    @47
    @55
    @34
    @31
    @73
    @74
    xp11
    sylancr
    @78
    @69
    @79
    @10
    @66
    @46
    sneqr
    adantr
    syl6bi
    adantr
    sylbid
    sylbid
    rgen2a
    vn
    vk
    com
    cvv
    cA
    dff13
    mpbir2an
    @62
    com
    @6
    cA
    wf1o
    com
    @6
    cen
    wbr
    @63
    com
    cvv
    cA
    f1f1orn
    com
    @6
    cA
    omex
    f1oen
    com
    @6
    ensym
    3syl
    va
    cv
    #
    com
    cen
    wbr
    #
    @5
    vz
    @81
    wral
    #
    vf
    wex
    #
    wi
    @63
    @64
    wi
    va
    @6
    @6
    vn
    com
    @35
    cmpt
    #
    crn
    #
    cvv
    cA
    @85
    axcc2lem.2
    rneqi
    @85
    cdm
    #
    cvv
    wcel
    @85
    wfun
    @86
    cvv
    wcel
    @87
    com
    cvv
    @39
    @87
    com
    wceq
    vn
    com
    vn
    com
    @35
    cvv
    dmmptg
    @39
    @29
    @41
    a1i
    mprg
    omex
    eqeltri
    vn
    com
    @35
    funmpt
    cvv
    @85
    funrnex
    mp2
    eqeltri
    @81
    @6
    wceq
    #
    @82
    @63
    @84
    @64
    @81
    @6
    com
    cen
    breq1
    @88
    @83
    @7
    vf
    @5
    vz
    @81
    @6
    raleq
    exbidv
    imbi12d
    va
    vz
    vf
    ax-cc
    vtocl
    mp2b
    exlimiiv
end
