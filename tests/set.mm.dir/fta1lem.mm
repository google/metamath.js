include "cfn.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "cdgr.mm"
include "cle.mm"
include "wbr.mm"
include "cidp.mm"
include "cc.mm"
include "csn.mm"
include "cxp.mm"
include "cmin.mm"
include "cof.mm"
include "co.mm"
include "cquot.mm"
include "ccnv.mm"
include "cc0.mm"
include "cima.mm"
include "cun.mm"
include "cmul.mm"
include "cply.mm"
include "wceq.mm"
include "c0p.mm"
include "wne.mm"
include "cdif.mm"
include "wa.mm"
include "eldifsn.mm"
include "sylib.mm"
include "simpld.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "plyf.mm"
include "ffn.mm"
include "fniniseg.mm"
include "4syl.mm"
include "mpbid.mm"
include "simprd.mm"
include "eqid.mm"
include "facth.mm"
include "syl3anc.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "cvv.mm"
include "cnex.mm"
include "a1i.mm"
include "wss.mm"
include "c1.mm"
include "ssid.mm"
include "ax-1cn.mm"
include "plyid.mm"
include "mp2an.mm"
include "plyconst.mm"
include "sylancr.mm"
include "plysubcl.mm"
include "syl.mm"
include "w3a.mm"
include "plyremlem.mm"
include "simp2d.mm"
include "ax-1ne0.mm"
include "eqnetrd.mm"
include "fveq2.mm"
include "dgr0.mm"
include "syl6eq.mm"
include "necon3i.mm"
include "quotcl2.mm"
include "ofmulrt.mm"
include "simp3d.mm"
include "uneq1d.mm"
include "3eqtrd.mm"
include "uncom.mm"
include "3eqtr4g.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "eqcomd.mm"
include "0cnd.mm"
include "mul01.mm"
include "adantl.mm"
include "caofid1.mm"
include "df-0p.mm"
include "oveq2i.mm"
include "3netr4d.mm"
include "oveq2.mm"
include "sylanbrc.mm"
include "cn0.mm"
include "dgrcl.mm"
include "nn0cnd.mm"
include "caddc.mm"
include "addcom.mm"
include "fveq2d.mm"
include "dgrmul.mm"
include "syl22anc.mm"
include "3eqtr3d.mm"
include "oveq1d.mm"
include "3eqtrrd.mm"
include "addcanad.mm"
include "eqeq1d.mm"
include "cnveq.mm"
include "eleq1d.mm"
include "breq12d.mm"
include "anbi12d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "snfi.mm"
include "unfi.mm"
include "sylancl.mm"
include "eqeltrd.mm"
include "hashcl.mm"
include "nn0red.mm"
include "cr.mm"
include "peano2re.mm"
include "hashun2.mm"
include "hashsng.mm"
include "oveq2d.mm"
include "breqtrd.mm"
include "1red.mm"
include "leadd1dd.mm"
include "breqtrrd.mm"
include "letrd.mm"
include "eqbrtrd.mm"
include "jca.mm"

theorem fta1lem
  let wph: wff ph
  let cA: class A
  let cD: class D
  let cR: class R
  let vg: setvar g
  let cF: class F
  let vx: setvar x
  let vd: setvar d
  let vf: setvar f
  assume fta1.1: |- R = ( `' F " { 0 } )
  assume fta1.2: |- ( ph -> D e. NN0 )
  assume fta1.3: |- ( ph -> F e. ( ( Poly ` CC ) \ { 0p } ) )
  assume fta1.4: |- ( ph -> ( deg ` F ) = ( D + 1 ) )
  assume fta1.5: |- ( ph -> A e. ( `' F " { 0 } ) )
  assume fta1.6: |- ( ph -> A. g e. ( ( Poly ` CC ) \ { 0p } ) ( ( deg ` g ) = D -> ( ( `' g " { 0 } ) e. Fin /\ ( # ` ( `' g " { 0 } ) ) <_ ( deg ` g ) ) ) )

  disjoint A g
  disjoint D g
  disjoint F g
  disjoint g x
  disjoint A x
  disjoint d f
  disjoint d g
  disjoint d x
  disjoint F d
  disjoint f g
  disjoint f x
  disjoint F f
  disjoint F x
  disjoint ph x
  disjoint R f
  assert |- ( ph -> ( R e. Fin /\ ( # ` R ) <_ ( deg ` F ) ) )

  proof
    wph
    cR
    cfn
    wcel
    cR
    chash
    cfv
    #
    cF
    cdgr
    cfv
    #
    cle
    wbr
    wph
    cR
    cF
    cidp
    cc
    cA
    csn
    #
    cxp
    #
    cmin
    cof
    co
    #
    cquot
    co
    #
    ccnv
    #
    cc0
    csn
    #
    cima
    #
    @2
    cun
    #
    cfn
    wph
    cF
    ccnv
    #
    @7
    cima
    #
    @2
    @8
    cun
    #
    cR
    @9
    wph
    @11
    @4
    @5
    cmul
    cof
    #
    co
    #
    ccnv
    #
    @7
    cima
    #
    @4
    ccnv
    @7
    cima
    #
    @8
    cun
    #
    @12
    wph
    @10
    @15
    @7
    wph
    cF
    @14
    wph
    cF
    cc
    cply
    cfv
    #
    wcel
    #
    cA
    cc
    wcel
    #
    cA
    cF
    cfv
    cc0
    wceq
    #
    cF
    @14
    wceq
    wph
    @20
    cF
    c0p
    wne
    #
    wph
    cF
    @19
    c0p
    csn
    cdif
    #
    wcel
    @20
    @23
    wa
    fta1.3
    cF
    @19
    c0p
    eldifsn
    sylib
    #
    simpld
    #
    wph
    @21
    @22
    wph
    cA
    @11
    wcel
    #
    @21
    @22
    wa
    #
    fta1.5
    wph
    @20
    cc
    cc
    cF
    wf
    cF
    cc
    wfn
    @27
    @28
    wb
    @26
    cc
    cF
    plyf
    cc
    cc
    cF
    ffn
    cc
    cc0
    cA
    cF
    fniniseg
    4syl
    mpbid
    #
    simpld
    #
    wph
    @21
    @22
    @29
    simprd
    cA
    cc
    cF
    @4
    @4
    eqid
    #
    facth
    syl3anc
    #
    cnveqd
    imaeq1d
    wph
    cc
    cvv
    wcel
    #
    cc
    cc
    @4
    wf
    #
    cc
    cc
    @5
    wf
    #
    @16
    @18
    wceq
    @33
    wph
    cnex
    a1i
    #
    wph
    @4
    @19
    wcel
    #
    @34
    wph
    cidp
    @19
    wcel
    #
    @3
    @19
    wcel
    #
    @37
    cc
    cc
    wss
    #
    c1
    cc
    wcel
    #
    @38
    cc
    ssid
    #
    ax-1cn
    cc
    plyid
    mp2an
    wph
    @40
    @21
    @39
    @42
    @30
    cA
    cc
    plyconst
    sylancr
    cc
    cidp
    @3
    plysubcl
    sylancr
    #
    cc
    @4
    plyf
    syl
    #
    wph
    @5
    @19
    wcel
    #
    @35
    wph
    @20
    @37
    @4
    c0p
    wne
    #
    @45
    @26
    @43
    wph
    @4
    cdgr
    cfv
    #
    cc0
    wne
    @46
    wph
    @47
    c1
    cc0
    wph
    @37
    @47
    c1
    wceq
    #
    @17
    @2
    wceq
    #
    wph
    @21
    @37
    @48
    @49
    w3a
    @30
    cA
    @4
    @31
    plyremlem
    syl
    #
    simp2d
    #
    c1
    cc0
    wne
    wph
    ax-1ne0
    a1i
    eqnetrd
    @4
    c0p
    @47
    cc0
    @4
    c0p
    wceq
    @47
    c0p
    cdgr
    cfv
    cc0
    @4
    c0p
    cdgr
    fveq2
    dgr0
    syl6eq
    necon3i
    syl
    #
    cc
    cF
    @4
    quotcl2
    syl3anc
    #
    cc
    @5
    plyf
    syl
    cc
    @4
    @5
    cvv
    ofmulrt
    syl3anc
    wph
    @17
    @2
    @8
    wph
    @37
    @48
    @49
    @50
    simp3d
    uneq1d
    3eqtrd
    fta1.1
    @8
    @2
    uncom
    3eqtr4g
    #
    wph
    @8
    cfn
    wcel
    #
    @2
    cfn
    wcel
    #
    @9
    cfn
    wcel
    #
    wph
    @55
    @8
    chash
    cfv
    #
    @5
    cdgr
    cfv
    #
    cle
    wbr
    #
    wph
    @5
    @24
    wcel
    #
    vg
    cv
    #
    cdgr
    cfv
    #
    cD
    wceq
    #
    @62
    ccnv
    #
    @7
    cima
    #
    cfn
    wcel
    #
    @66
    chash
    cfv
    #
    @63
    cle
    wbr
    #
    wa
    #
    wi
    #
    vg
    @24
    wral
    @59
    cD
    wceq
    #
    @55
    @60
    wa
    #
    wph
    @45
    @5
    c0p
    wne
    #
    @61
    @53
    wph
    @14
    @4
    c0p
    @13
    co
    #
    wne
    @74
    wph
    cF
    c0p
    @14
    @75
    wph
    @20
    @23
    @25
    simprd
    wph
    cF
    @14
    @32
    eqcomd
    wph
    @4
    cc
    @7
    cxp
    #
    @13
    co
    @76
    @75
    c0p
    wph
    vx
    cc
    cc0
    cc0
    cmul
    cc
    @4
    cvv
    cc
    cc
    @36
    @44
    wph
    0cnd
    #
    @77
    vx
    cv
    #
    cc
    wcel
    @78
    cc0
    cmul
    co
    cc0
    wceq
    wph
    @78
    mul01
    adantl
    caofid1
    c0p
    @76
    @4
    @13
    df-0p
    oveq2i
    df-0p
    3eqtr4g
    3netr4d
    @5
    c0p
    @14
    @75
    @5
    c0p
    @4
    @13
    oveq2
    necon3i
    syl
    #
    @5
    @19
    c0p
    eldifsn
    sylanbrc
    fta1.6
    wph
    c1
    @59
    cD
    @41
    wph
    ax-1cn
    a1i
    wph
    @59
    wph
    @45
    @59
    cn0
    wcel
    @53
    cc
    @5
    dgrcl
    syl
    nn0cnd
    wph
    cD
    fta1.2
    nn0cnd
    #
    wph
    c1
    cD
    caddc
    co
    #
    cD
    c1
    caddc
    co
    #
    @47
    @59
    caddc
    co
    #
    c1
    @59
    caddc
    co
    wph
    @41
    cD
    cc
    wcel
    @81
    @82
    wceq
    ax-1cn
    @80
    c1
    cD
    addcom
    sylancr
    wph
    @1
    @14
    cdgr
    cfv
    #
    @82
    @83
    wph
    cF
    @14
    cdgr
    @32
    fveq2d
    fta1.4
    wph
    @37
    @46
    @45
    @74
    @84
    @83
    wceq
    @43
    @52
    @53
    @79
    cc
    @4
    @5
    @47
    @59
    @47
    eqid
    @59
    eqid
    dgrmul
    syl22anc
    3eqtr3d
    wph
    @47
    c1
    @59
    caddc
    @51
    oveq1d
    3eqtrrd
    addcanad
    #
    @71
    @72
    @73
    wi
    vg
    @5
    @24
    @62
    @5
    wceq
    #
    @64
    @72
    @70
    @73
    @86
    @63
    @59
    cD
    @62
    @5
    cdgr
    fveq2
    #
    eqeq1d
    @86
    @67
    @55
    @69
    @60
    @86
    @66
    @8
    cfn
    @86
    @65
    @6
    @7
    @62
    @5
    cnveq
    imaeq1d
    #
    eleq1d
    @86
    @68
    @58
    @63
    @59
    cle
    @86
    @66
    @8
    chash
    @88
    fveq2d
    @87
    breq12d
    anbi12d
    imbi12d
    rspcv
    syl3c
    #
    simpld
    #
    cA
    snfi
    #
    @8
    @2
    unfi
    sylancl
    #
    eqeltrd
    wph
    @0
    @9
    chash
    cfv
    #
    @1
    cle
    wph
    cR
    @9
    chash
    @54
    fveq2d
    wph
    @93
    @58
    c1
    caddc
    co
    #
    @1
    wph
    @93
    wph
    @57
    @93
    cn0
    wcel
    @92
    @9
    hashcl
    syl
    nn0red
    wph
    @58
    cr
    wcel
    @94
    cr
    wcel
    wph
    @58
    wph
    @55
    @58
    cn0
    wcel
    @90
    @8
    hashcl
    syl
    nn0red
    #
    @58
    peano2re
    syl
    wph
    @1
    wph
    @20
    @1
    cn0
    wcel
    @26
    cc
    cF
    dgrcl
    syl
    nn0red
    wph
    @93
    @58
    @2
    chash
    cfv
    #
    caddc
    co
    #
    @94
    cle
    wph
    @55
    @56
    @93
    @97
    cle
    wbr
    @90
    @91
    @8
    @2
    hashun2
    sylancl
    wph
    @96
    c1
    @58
    caddc
    wph
    @21
    @96
    c1
    wceq
    @30
    cA
    cc
    hashsng
    syl
    oveq2d
    breqtrd
    wph
    @94
    @82
    @1
    cle
    wph
    @58
    cD
    c1
    @95
    wph
    cD
    fta1.2
    nn0red
    wph
    1red
    wph
    @58
    @59
    cD
    cle
    wph
    @55
    @60
    @89
    simprd
    @85
    breqtrd
    leadd1dd
    fta1.4
    breqtrrd
    letrd
    eqbrtrd
    jca
end
