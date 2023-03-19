include "cmpt.mm"
include "crn.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wf.mm"
include "anassrs.mm"
include "an32s.mm"
include "eqid.mm"
include "fmptd.mm"
include "frn.mm"
include "syl.mm"
include "cdm.mm"
include "cuz.mm"
include "cfv.mm"
include "cz.mm"
include "uzid.mm"
include "syl6eleqr.mm"
include "adantr.mm"
include "dmmptd.mm"
include "eleqtrrd.mm"
include "ne0i.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "sylib.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "breq1.mm"
include "ralrn.mm"
include "nffvmpt1.mm"
include "nfcv.mm"
include "nfbr.mm"
include "nfv.mm"
include "weq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "cbvral.mm"
include "wceq.mm"
include "simpr.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "ralbidva.mm"
include "syl5bb.mm"
include "bitrd.mm"
include "rexbidv.mm"
include "mpbird.mm"
include "suprcl.mm"
include "syl3anc.mm"
include "ccnv.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "cima.mm"
include "ciun.mm"
include "cvol.mm"
include "cvv.mm"
include "ltso.mm"
include "supex.mm"
include "sylancl.mm"
include "breq2d.mm"
include "w3a.mm"
include "3jca.mm"
include "adantlr.mm"
include "simplr.mm"
include "suprlub.mm"
include "breq2.mm"
include "rexrn.mm"
include "cbvrex.mm"
include "cid.mm"
include "fvmpt2i.mm"
include "adantl.mm"
include "eqcomd.mm"
include "sylan9eqr.mm"
include "rexbidva.mm"
include "3bitrd.mm"
include "ralrimiva.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "nfrex.mm"
include "nfbi.mm"
include "bibi12d.mm"
include "r19.21bi.mm"
include "cxr.mm"
include "rexr.mm"
include "ad2antlr.mm"
include "elioopnf.mm"
include "ffvelrnda.mm"
include "biantrurd.mm"
include "bitr4d.mm"
include "adantllr.mm"
include "3bitr4d.mm"
include "pm5.32da.mm"
include "elpreima.mm"
include "eliun.mm"
include "r19.42v.mm"
include "syl6bb.mm"
include "eqrdv.mm"
include "cn.mm"
include "cdom.mm"
include "cen.mm"
include "zex.mm"
include "uzssz.mm"
include "ssdomg.mm"
include "mp2.mm"
include "eqbrtri.mm"
include "znnen.mm"
include "domentr.mm"
include "mp2an.mm"
include "cmbf.mm"
include "mbfima.mm"
include "iunmbl2.mm"
include "sylancr.mm"
include "eqeltrd.mm"
include "ismbf3d.mm"

theorem mbfsup
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vn: setvar n
  let cG: class G
  let cM: class M
  let cZ: class Z
  let vm: setvar m
  let vz: setvar z
  let vt: setvar t
  assume mbfsup.1: |- Z = ( ZZ>= ` M )
  assume mbfsup.2: |- G = ( x e. A |-> sup ( ran ( n e. Z |-> B ) , RR , < ) )
  assume mbfsup.3: |- ( ph -> M e. ZZ )
  assume mbfsup.4: |- ( ( ph /\ n e. Z ) -> ( x e. A |-> B ) e. MblFn )
  assume mbfsup.5: |- ( ( ph /\ ( n e. Z /\ x e. A ) ) -> B e. RR )
  assume mbfsup.6: |- ( ( ph /\ x e. A ) -> E. y e. RR A. n e. Z B <_ y )

  disjoint n x
  disjoint n y
  disjoint A n
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint Z n
  disjoint Z x
  disjoint Z y
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n z
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B m
  disjoint B z
  disjoint n t
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint ph t
  disjoint ph z
  disjoint Z m
  disjoint Z z
  disjoint m t
  disjoint G m
  disjoint G t
  disjoint G z
  assert |- ( ph -> G e. MblFn )

  proof
    wph
    vt
    cA
    cG
    wph
    vx
    cA
    vn
    cZ
    cB
    cmpt
    #
    crn
    #
    cr
    clt
    csup
    #
    cr
    cG
    wph
    vx
    cv
    #
    cA
    wcel
    #
    wa
    #
    @1
    cr
    wss
    #
    @1
    c0
    wne
    #
    vz
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vz
    @1
    wral
    #
    vy
    cr
    wrex
    #
    @2
    cr
    wcel
    @5
    cZ
    cr
    @0
    wf
    #
    @6
    @5
    vn
    cZ
    cB
    cr
    @0
    wph
    vn
    cv
    #
    cZ
    wcel
    #
    @4
    cB
    cr
    wcel
    #
    wph
    @15
    @4
    @16
    mbfsup.5
    anassrs
    #
    an32s
    #
    @0
    eqid
    #
    fmptd
    #
    cZ
    cr
    @0
    frn
    syl
    #
    @5
    @0
    cdm
    #
    c0
    wne
    #
    @7
    @5
    cM
    @22
    wcel
    @23
    @5
    cM
    cZ
    @22
    wph
    cM
    cZ
    wcel
    @4
    wph
    cM
    cM
    cuz
    cfv
    #
    cZ
    wph
    cM
    cz
    wcel
    cM
    @24
    wcel
    mbfsup.3
    cM
    uzid
    syl
    mbfsup.1
    syl6eleqr
    adantr
    @5
    vn
    @0
    cZ
    cB
    cr
    @19
    @18
    dmmptd
    eleqtrrd
    @22
    cM
    ne0i
    syl
    @22
    c0
    @1
    c0
    @0
    dm0rn0
    necon3bii
    sylib
    #
    @5
    @12
    cB
    @9
    cle
    wbr
    #
    vn
    cZ
    wral
    #
    vy
    cr
    wrex
    mbfsup.6
    @5
    @11
    @27
    vy
    cr
    @5
    @11
    vm
    cv
    #
    @0
    cfv
    #
    @9
    cle
    wbr
    #
    vm
    cZ
    wral
    #
    @27
    @5
    @0
    cZ
    wfn
    #
    @11
    @31
    wb
    @5
    @13
    @32
    @20
    cZ
    cr
    @0
    ffn
    syl
    #
    @10
    @30
    vz
    vm
    cZ
    @0
    @8
    @29
    @9
    cle
    breq1
    ralrn
    syl
    @31
    @14
    @0
    cfv
    #
    @9
    cle
    wbr
    #
    vn
    cZ
    wral
    @5
    @27
    @30
    @35
    vm
    vn
    cZ
    vn
    @29
    @9
    cle
    vn
    cZ
    cB
    @28
    nffvmpt1
    #
    vn
    cle
    nfcv
    vn
    @9
    nfcv
    nfbr
    @35
    vm
    nfv
    vm
    vn
    weq
    #
    @29
    @34
    @9
    cle
    @28
    @14
    @0
    fveq2
    #
    breq1d
    cbvral
    @5
    @35
    @26
    vn
    cZ
    @5
    @15
    wa
    #
    @34
    cB
    @9
    cle
    @39
    @15
    @16
    @34
    cB
    wceq
    @5
    @15
    simpr
    @18
    vn
    cZ
    cB
    cr
    @0
    @19
    fvmpt2
    syl2anc
    breq1d
    ralbidva
    syl5bb
    bitrd
    rexbidv
    mpbird
    #
    vy
    vz
    @1
    suprcl
    syl3anc
    mbfsup.2
    fmptd
    #
    wph
    vt
    cv
    #
    cr
    wcel
    #
    wa
    #
    cG
    ccnv
    @42
    cpnf
    cioo
    co
    #
    cima
    #
    vn
    cZ
    vx
    cA
    cB
    cmpt
    #
    ccnv
    @45
    cima
    #
    ciun
    #
    cvol
    cdm
    #
    @44
    vz
    @46
    @49
    @44
    @8
    cA
    wcel
    #
    @8
    cG
    cfv
    #
    @45
    wcel
    #
    wa
    #
    @51
    @8
    @47
    cfv
    #
    @45
    wcel
    #
    vn
    cZ
    wrex
    #
    wa
    #
    @8
    @46
    wcel
    #
    @8
    @49
    wcel
    #
    @44
    @51
    @53
    @57
    @44
    @51
    wa
    #
    @42
    @52
    clt
    wbr
    #
    @42
    @55
    clt
    wbr
    #
    vn
    cZ
    wrex
    #
    @53
    @57
    @44
    @62
    @64
    wb
    #
    vz
    cA
    @44
    @42
    @3
    cG
    cfv
    #
    clt
    wbr
    #
    @42
    @3
    @47
    cfv
    #
    clt
    wbr
    #
    vn
    cZ
    wrex
    #
    wb
    #
    vx
    cA
    wral
    @65
    vz
    cA
    wral
    @44
    @71
    vx
    cA
    @44
    @4
    wa
    #
    @67
    @42
    @2
    clt
    wbr
    #
    @42
    @8
    clt
    wbr
    #
    vz
    @1
    wrex
    #
    @70
    @72
    @66
    @2
    @42
    clt
    @72
    @4
    @2
    cvv
    wcel
    @66
    @2
    wceq
    @44
    @4
    simpr
    cr
    @1
    clt
    ltso
    supex
    vx
    cA
    @2
    cvv
    cG
    mbfsup.2
    fvmpt2
    sylancl
    breq2d
    @72
    @6
    @7
    @12
    w3a
    #
    @43
    @73
    @75
    wb
    wph
    @4
    @76
    @43
    @5
    @6
    @7
    @12
    @21
    @25
    @40
    3jca
    adantlr
    wph
    @43
    @4
    simplr
    vy
    vz
    vz
    @1
    @42
    suprlub
    syl2anc
    @72
    @75
    @42
    @29
    clt
    wbr
    #
    vm
    cZ
    wrex
    #
    @70
    @72
    @32
    @75
    @78
    wb
    wph
    @4
    @32
    @43
    @33
    adantlr
    @74
    @77
    vz
    vm
    cZ
    @0
    @8
    @29
    @42
    clt
    breq2
    rexrn
    syl
    @78
    @42
    @34
    clt
    wbr
    #
    vn
    cZ
    wrex
    #
    @72
    @70
    @77
    @79
    vm
    vn
    cZ
    vn
    @42
    @29
    clt
    vn
    @42
    nfcv
    vn
    clt
    nfcv
    @36
    nfbr
    @79
    vm
    nfv
    @37
    @29
    @34
    @42
    clt
    @38
    breq2d
    cbvrex
    wph
    @4
    @80
    @70
    wb
    @43
    @5
    @79
    @69
    vn
    cZ
    @39
    @34
    @68
    @42
    clt
    @15
    @5
    @34
    cB
    cid
    cfv
    #
    @68
    vn
    cZ
    cB
    @0
    @19
    fvmpt2i
    @5
    @68
    @81
    @4
    @68
    @81
    wceq
    wph
    vx
    cA
    cB
    @47
    @47
    eqid
    #
    fvmpt2i
    adantl
    eqcomd
    sylan9eqr
    breq2d
    rexbidva
    adantlr
    syl5bb
    bitrd
    3bitrd
    ralrimiva
    @71
    @65
    vx
    vz
    cA
    @71
    vz
    nfv
    @62
    @64
    vx
    vx
    @42
    @52
    clt
    vx
    @42
    nfcv
    #
    vx
    clt
    nfcv
    #
    vx
    @8
    cG
    vx
    cG
    vx
    cA
    @2
    cmpt
    mbfsup.2
    vx
    cA
    @2
    nfmpt1
    nfcxfr
    vx
    @8
    nfcv
    nffv
    nfbr
    @63
    vx
    vn
    cZ
    vx
    cZ
    nfcv
    vx
    @42
    @55
    clt
    @83
    @84
    vx
    cA
    cB
    @8
    nffvmpt1
    nfbr
    nfrex
    nfbi
    vx
    vz
    weq
    #
    @67
    @62
    @70
    @64
    @85
    @66
    @52
    @42
    clt
    @3
    @8
    cG
    fveq2
    breq2d
    @85
    @69
    @63
    vn
    cZ
    @85
    @68
    @55
    @42
    clt
    @3
    @8
    @47
    fveq2
    breq2d
    rexbidv
    bibi12d
    cbvral
    sylib
    r19.21bi
    @61
    @53
    @52
    cr
    wcel
    #
    @62
    wa
    #
    @62
    @61
    @42
    cxr
    wcel
    #
    @53
    @87
    wb
    @43
    @88
    wph
    @51
    @42
    rexr
    ad2antlr
    #
    @42
    @52
    elioopnf
    syl
    @61
    @86
    @62
    @44
    cA
    cr
    @8
    cG
    wph
    cA
    cr
    cG
    wf
    #
    @43
    @41
    adantr
    ffvelrnda
    biantrurd
    bitr4d
    @61
    @56
    @63
    vn
    cZ
    @61
    @15
    wa
    #
    @56
    @55
    cr
    wcel
    #
    @63
    wa
    #
    @63
    @91
    @88
    @56
    @93
    wb
    @61
    @88
    @15
    @89
    adantr
    @42
    @55
    elioopnf
    syl
    wph
    @51
    @15
    @63
    @93
    wb
    #
    @43
    wph
    @15
    @51
    @94
    wph
    @15
    wa
    #
    @51
    wa
    @92
    @63
    @95
    cA
    cr
    @8
    @47
    @95
    vx
    cA
    cB
    cr
    @47
    @17
    @82
    fmptd
    #
    ffvelrnda
    biantrurd
    an32s
    adantllr
    bitr4d
    rexbidva
    3bitr4d
    pm5.32da
    @44
    cG
    cA
    wfn
    #
    @59
    @54
    wb
    wph
    @97
    @43
    wph
    @90
    @97
    @41
    cA
    cr
    cG
    ffn
    syl
    adantr
    cA
    @8
    @45
    cG
    elpreima
    syl
    @60
    @8
    @48
    wcel
    #
    vn
    cZ
    wrex
    #
    @44
    @58
    vn
    @8
    cZ
    @48
    eliun
    @44
    @99
    @51
    @56
    wa
    #
    vn
    cZ
    wrex
    #
    @58
    wph
    @99
    @101
    wb
    @43
    wph
    @98
    @100
    vn
    cZ
    @95
    @47
    cA
    wfn
    #
    @98
    @100
    wb
    @95
    cA
    cr
    @47
    wf
    #
    @102
    @96
    cA
    cr
    @47
    ffn
    syl
    cA
    @8
    @45
    @47
    elpreima
    syl
    rexbidva
    adantr
    @51
    @56
    vn
    cZ
    r19.42v
    syl6bb
    syl5bb
    3bitr4d
    eqrdv
    @44
    cZ
    cn
    cdom
    wbr
    #
    @48
    @50
    wcel
    #
    vn
    cZ
    wral
    #
    @49
    @50
    wcel
    cZ
    cz
    cdom
    wbr
    cz
    cn
    cen
    wbr
    @104
    cZ
    @24
    cz
    cdom
    mbfsup.1
    cz
    cvv
    wcel
    @24
    cz
    wss
    @24
    cz
    cdom
    wbr
    zex
    cM
    uzssz
    @24
    cz
    cvv
    ssdomg
    mp2
    eqbrtri
    znnen
    cZ
    cz
    cn
    domentr
    mp2an
    wph
    @106
    @43
    wph
    @105
    vn
    cZ
    @95
    @47
    cmbf
    wcel
    @103
    @105
    mbfsup.4
    @96
    cA
    @42
    cpnf
    @47
    mbfima
    syl2anc
    ralrimiva
    adantr
    cZ
    @48
    vn
    iunmbl2
    sylancr
    eqeltrd
    ismbf3d
end
