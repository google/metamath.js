include "cms.mm"
include "cfv.mm"
include "wcel.mm"
include "cn.mm"
include "wf.mm"
include "cv.mm"
include "ccl.mm"
include "wceq.mm"
include "wral.mm"
include "crn.mm"
include "cint.mm"
include "wa.mm"
include "cdif.mm"
include "cmpt.mm"
include "cnt.mm"
include "c0.mm"
include "cuni.mm"
include "cxmt.mm"
include "wi.mm"
include "cme.mm"
include "cmetmet.mm"
include "metxmet.mm"
include "syl.mm"
include "ctop.mm"
include "wss.mm"
include "mopntop.mm"
include "ad2antrr.mm"
include "ffvelrn.mm"
include "elssuni.mm"
include "adantll.mm"
include "eqid.mm"
include "clsval2.mm"
include "syl2anc.mm"
include "mopnuni.mm"
include "eqeq12d.mm"
include "difeq2.mm"
include "difid.mm"
include "syl6eq.mm"
include "difss.mm"
include "ntropn.mm"
include "sylancl.mm"
include "dfss4.mm"
include "sylib.mm"
include "cvv.mm"
include "id.mm"
include "cdm.mm"
include "elfvdm.mm"
include "difexg.mm"
include "adantr.mm"
include "fveq2.mm"
include "difeq2d.mm"
include "fvmptg.mm"
include "syl2anr.mm"
include "difeq1d.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "eqtr4d.mm"
include "eqeq1d.mm"
include "syl5ib.mm"
include "sylbid.mm"
include "ralimdva.mm"
include "sylan.mm"
include "ccld.mm"
include "opncld.mm"
include "eqeltrd.mm"
include "sylan2.mm"
include "anassrs.mm"
include "ralrimiva.mm"
include "fmpt.mm"
include "wne.mm"
include "wrex.mm"
include "wn.mm"
include "nne.mm"
include "ralbii.mm"
include "ralnex.mm"
include "bitr3i.mm"
include "bcth.mm"
include "3expia.mm"
include "necon1bd.mm"
include "syl5bi.mm"
include "syldan.mm"
include "ciin.mm"
include "ciun.mm"
include "wfn.mm"
include "fnmpt.mm"
include "fniunfv.mm"
include "3syl.mm"
include "iuneq2dv.mm"
include "cbviunv.mm"
include "syl6eqr.mm"
include "eqtr3d.mm"
include "iundif2.mm"
include "ffn.mm"
include "adantl.mm"
include "fniinfv.mm"
include "3eqtrd.mm"
include "c1.mm"
include "1nn.mm"
include "biidd.mm"
include "fnfvelrn.mm"
include "intss1.mm"
include "sstrd.mm"
include "expcom.mm"
include "vtoclga.mm"
include "ax-mp.mm"
include "dif0.mm"
include "syl6reqr.mm"
include "3syld.mm"
include "3impia.mm"

theorem bcth3
  let cD: class D
  let vk: setvar k
  let cJ: class J
  let cM: class M
  let cX: class X
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let vg: setvar g
  let vm: setvar m
  let vy: setvar y
  let cF: class F
  let wph: wff ph
  let cR: class R
  assume bcth.2: |- J = ( MetOpen ` D )

  disjoint D k
  disjoint J k
  disjoint M k
  disjoint X k
  disjoint k n
  disjoint k r
  disjoint k x
  disjoint k z
  disjoint A k
  disjoint n r
  disjoint n x
  disjoint n z
  disjoint A n
  disjoint r x
  disjoint r z
  disjoint A r
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint B k
  disjoint B r
  disjoint B x
  disjoint B z
  disjoint C r
  disjoint C x
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g r
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint D g
  disjoint k m
  disjoint k y
  disjoint m n
  disjoint m r
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint D m
  disjoint n y
  disjoint D n
  disjoint r y
  disjoint D r
  disjoint x y
  disjoint D x
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint F g
  disjoint F k
  disjoint F n
  disjoint F r
  disjoint F x
  disjoint F z
  disjoint J g
  disjoint J m
  disjoint J n
  disjoint J r
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint M g
  disjoint M m
  disjoint M n
  disjoint M r
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint ph r
  disjoint ph x
  disjoint ph z
  disjoint R x
  disjoint X g
  disjoint X m
  disjoint X n
  disjoint X r
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ( D e. ( CMet ` X ) /\ M : NN --> J /\ A. k e. NN ( ( cls ` J ) ` ( M ` k ) ) = X ) -> ( ( cls ` J ) ` |^| ran M ) = X )

  proof
    cD
    cX
    cms
    cfv
    wcel
    #
    cn
    cJ
    cM
    wf
    #
    vk
    cv
    #
    cM
    cfv
    #
    cJ
    ccl
    cfv
    #
    cfv
    #
    cX
    wceq
    #
    vk
    cn
    wral
    #
    cM
    crn
    #
    cint
    #
    @4
    cfv
    #
    cX
    wceq
    #
    @0
    @1
    wa
    #
    @7
    @2
    vx
    cn
    cX
    vx
    cv
    #
    cM
    cfv
    #
    cdif
    #
    cmpt
    #
    cfv
    #
    cJ
    cnt
    cfv
    #
    cfv
    #
    c0
    wceq
    #
    vk
    cn
    wral
    #
    @16
    crn
    cuni
    #
    @18
    cfv
    #
    c0
    wceq
    #
    @11
    @0
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @1
    @7
    @21
    wi
    @0
    cD
    cX
    cme
    cfv
    wcel
    @25
    cD
    cX
    cmetmet
    cD
    cX
    metxmet
    syl
    #
    @25
    @1
    wa
    #
    @6
    @20
    vk
    cn
    @27
    @2
    cn
    wcel
    #
    wa
    #
    @6
    cJ
    cuni
    #
    @30
    @3
    cdif
    #
    @18
    cfv
    #
    cdif
    #
    @30
    wceq
    #
    @20
    @29
    @5
    @33
    cX
    @30
    @29
    cJ
    ctop
    wcel
    #
    @3
    @30
    wss
    #
    @5
    @33
    wceq
    @25
    @35
    @1
    @28
    cD
    cJ
    cX
    bcth.2
    mopntop
    #
    ad2antrr
    #
    @1
    @28
    @36
    @25
    @1
    @28
    wa
    @3
    cJ
    wcel
    @36
    cn
    cJ
    @2
    cM
    ffvelrn
    @3
    cJ
    elssuni
    syl
    adantll
    #
    @3
    cJ
    @30
    @30
    eqid
    #
    clsval2
    syl2anc
    @25
    cX
    @30
    wceq
    #
    @1
    @28
    cD
    cJ
    cX
    bcth.2
    mopnuni
    #
    ad2antrr
    #
    eqeq12d
    @34
    @30
    @33
    cdif
    #
    c0
    wceq
    @29
    @20
    @34
    @44
    @30
    @30
    cdif
    c0
    @33
    @30
    @30
    difeq2
    @30
    difid
    syl6eq
    @29
    @44
    @19
    c0
    @29
    @44
    @32
    @19
    @29
    @32
    @30
    wss
    #
    @44
    @32
    wceq
    @29
    @32
    cJ
    wcel
    #
    @45
    @29
    @35
    @31
    @30
    wss
    @46
    @38
    @30
    @3
    difss
    @31
    cJ
    @30
    @40
    ntropn
    sylancl
    @32
    cJ
    elssuni
    syl
    @32
    @30
    dfss4
    sylib
    @29
    @17
    @31
    @18
    @29
    @17
    cX
    @3
    cdif
    #
    @31
    @28
    @28
    @47
    cvv
    wcel
    #
    @17
    @47
    wceq
    @27
    @28
    id
    @25
    @48
    @1
    @25
    cX
    cxmt
    cdm
    #
    wcel
    #
    @48
    cD
    cX
    cxmt
    elfvdm
    #
    cX
    @3
    @49
    difexg
    syl
    adantr
    vx
    @2
    @15
    @47
    cn
    cvv
    @16
    @13
    @2
    wceq
    @14
    @3
    cX
    @13
    @2
    cM
    fveq2
    difeq2d
    #
    @16
    eqid
    #
    fvmptg
    syl2anr
    #
    @29
    cX
    @30
    @3
    @43
    difeq1d
    eqtrd
    fveq2d
    eqtr4d
    eqeq1d
    syl5ib
    sylbid
    ralimdva
    sylan
    @0
    @1
    cn
    cJ
    ccld
    cfv
    #
    @16
    wf
    #
    @21
    @24
    wi
    @12
    @15
    @55
    wcel
    #
    vx
    cn
    wral
    #
    @56
    @0
    @25
    @1
    @58
    @26
    @27
    @57
    vx
    cn
    @25
    @1
    @13
    cn
    wcel
    #
    @57
    @1
    @59
    wa
    @25
    @14
    cJ
    wcel
    #
    @57
    cn
    cJ
    @13
    cM
    ffvelrn
    @25
    @60
    wa
    @15
    @30
    @14
    cdif
    #
    @55
    @25
    @15
    @61
    wceq
    @60
    @25
    cX
    @30
    @14
    @42
    difeq1d
    adantr
    @25
    @35
    @60
    @61
    @55
    wcel
    @37
    @14
    cJ
    @30
    @40
    opncld
    sylan
    eqeltrd
    sylan2
    anassrs
    ralrimiva
    sylan
    vx
    cn
    @55
    @15
    @16
    @53
    fmpt
    sylib
    @21
    @19
    c0
    wne
    #
    vk
    cn
    wrex
    #
    wn
    #
    @0
    @56
    wa
    #
    @24
    @21
    @62
    wn
    #
    vk
    cn
    wral
    @64
    @66
    @20
    vk
    cn
    @19
    c0
    nne
    ralbii
    @62
    vk
    cn
    ralnex
    bitr3i
    @65
    @63
    @23
    c0
    @0
    @56
    @23
    c0
    wne
    @63
    cD
    vk
    cJ
    @16
    cX
    bcth.2
    bcth
    3expia
    necon1bd
    syl5bi
    syldan
    @0
    @25
    @1
    @24
    @11
    wi
    @26
    @24
    @30
    @23
    cdif
    #
    @30
    c0
    cdif
    #
    wceq
    @27
    @11
    @23
    c0
    @30
    difeq2
    @27
    @67
    @10
    @68
    cX
    @27
    @67
    @30
    @30
    @9
    cdif
    #
    @18
    cfv
    #
    cdif
    #
    @10
    @27
    @23
    @70
    @30
    @27
    @22
    @69
    @18
    @27
    @22
    cX
    vx
    cn
    @14
    ciin
    #
    cdif
    #
    cX
    @9
    cdif
    @69
    @27
    @22
    vx
    cn
    @15
    ciun
    #
    @73
    @27
    vk
    cn
    @17
    ciun
    #
    @22
    @74
    @27
    @15
    cvv
    wcel
    #
    vx
    cn
    wral
    @16
    cn
    wfn
    @75
    @22
    wceq
    @27
    @76
    vx
    cn
    @25
    @76
    @1
    @59
    @25
    @50
    @76
    @51
    cX
    @14
    @49
    difexg
    syl
    ad2antrr
    ralrimiva
    vx
    cn
    @15
    @16
    cvv
    @53
    fnmpt
    vk
    cn
    @16
    fniunfv
    3syl
    @27
    @75
    vk
    cn
    @47
    ciun
    @74
    @27
    vk
    cn
    @17
    @47
    @54
    iuneq2dv
    vx
    vk
    cn
    @15
    @47
    @52
    cbviunv
    syl6eqr
    eqtr3d
    vx
    cn
    cX
    @14
    iundif2
    syl6eq
    @27
    @72
    @9
    cX
    @27
    cM
    cn
    wfn
    #
    @72
    @9
    wceq
    @1
    @77
    @25
    cn
    cJ
    cM
    ffn
    adantl
    #
    vx
    cn
    cM
    fniinfv
    syl
    difeq2d
    @27
    cX
    @30
    @9
    @25
    @41
    @1
    @42
    adantr
    #
    difeq1d
    3eqtrd
    fveq2d
    difeq2d
    @27
    @35
    @9
    @30
    wss
    #
    @10
    @71
    wceq
    @25
    @35
    @1
    @37
    adantr
    c1
    cn
    wcel
    @27
    @80
    wi
    #
    1nn
    @81
    @81
    vk
    c1
    cn
    @2
    c1
    wceq
    @81
    biidd
    @27
    @28
    @80
    @29
    @9
    @3
    @30
    @29
    @3
    @8
    wcel
    #
    @9
    @3
    wss
    @27
    @77
    @28
    @82
    @78
    cn
    @2
    cM
    fnfvelrn
    sylan
    @3
    @8
    intss1
    syl
    @39
    sstrd
    expcom
    vtoclga
    ax-mp
    @9
    cJ
    @30
    @40
    clsval2
    syl2anc
    eqtr4d
    @27
    cX
    @30
    @68
    @79
    @30
    dif0
    syl6reqr
    eqeq12d
    syl5ib
    sylan
    3syld
    3impia
end
