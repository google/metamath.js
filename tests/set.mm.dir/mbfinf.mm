include "cneg.mm"
include "cmpt.mm"
include "crn.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cmbf.mm"
include "cinf.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "crab.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "wceq.mm"
include "wf.mm"
include "anass1rs.mm"
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
include "breq2.mm"
include "ralrn.mm"
include "nfcv.mm"
include "nffvmpt1.mm"
include "nfbr.mm"
include "nfv.mm"
include "fveq2.mm"
include "breq2d.mm"
include "cbvral.mm"
include "simpr.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "ralbidva.mm"
include "syl5bb.mm"
include "bitrd.mm"
include "rexbidv.mm"
include "mpbird.mm"
include "infrenegsup.mm"
include "syl3anc.mm"
include "wal.mm"
include "rabid.mm"
include "cc.mm"
include "recnd.mm"
include "adantlr.mm"
include "simplr.mm"
include "negcon2.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "eqeq1d.mm"
include "cvv.mm"
include "negex.mm"
include "mpan2.mm"
include "adantl.mm"
include "3bitr4d.mm"
include "ralrimiva.mm"
include "nfeq1.mm"
include "nfbi.mm"
include "bibi12d.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "rexbidva.mm"
include "fvelrnb.mm"
include "renegcld.mm"
include "pm5.32da.mm"
include "sseld.mm"
include "pm4.71rd.mm"
include "bitr4d.mm"
include "alrimiv.mm"
include "nfrab1.mm"
include "cleqf.mm"
include "supeq1d.mm"
include "negeqd.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "syl5eq.mm"
include "ltso.mm"
include "supex.mm"
include "a1i.mm"
include "anassrs.mm"
include "mbfneg.mm"
include "renegcl.mm"
include "ad2antrl.mm"
include "lenegd.mm"
include "biimpd.mm"
include "impr.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "rexlimddv.mm"
include "mbfsup.mm"
include "eqeltrd.mm"

theorem mbfinf
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
  let vr: setvar r
  let vz: setvar z
  assume mbfinf.1: |- Z = ( ZZ>= ` M )
  assume mbfinf.2: |- G = ( x e. A |-> inf ( ran ( n e. Z |-> B ) , RR , < ) )
  assume mbfinf.3: |- ( ph -> M e. ZZ )
  assume mbfinf.4: |- ( ( ph /\ n e. Z ) -> ( x e. A |-> B ) e. MblFn )
  assume mbfinf.5: |- ( ( ph /\ ( n e. Z /\ x e. A ) ) -> B e. RR )
  assume mbfinf.6: |- ( ( ph /\ x e. A ) -> E. y e. RR A. n e. Z y <_ B )

  disjoint n x
  disjoint n y
  disjoint A n
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint Z n
  disjoint Z x
  disjoint Z y
  disjoint B y
  disjoint m n
  disjoint m r
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n r
  disjoint n z
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint m ph
  disjoint ph r
  disjoint ph z
  disjoint Z m
  disjoint Z r
  disjoint Z z
  disjoint B m
  disjoint B r
  disjoint B z
  assert |- ( ph -> G e. MblFn )

  proof
    wph
    cG
    vx
    cA
    vn
    cZ
    cB
    cneg
    #
    cmpt
    #
    crn
    #
    cr
    clt
    csup
    #
    cneg
    #
    cmpt
    #
    cmbf
    wph
    cG
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
    cinf
    #
    cmpt
    @5
    mbfinf.2
    wph
    vx
    cA
    @8
    @4
    wph
    vx
    cv
    cA
    wcel
    #
    wa
    #
    @8
    vr
    cv
    #
    cneg
    #
    @7
    wcel
    #
    vr
    cr
    crab
    #
    cr
    clt
    csup
    #
    cneg
    #
    @4
    @10
    @7
    cr
    wss
    #
    @7
    c0
    wne
    #
    vy
    cv
    #
    vz
    cv
    #
    cle
    wbr
    #
    vz
    @7
    wral
    #
    vy
    cr
    wrex
    #
    @8
    @16
    wceq
    @10
    cZ
    cr
    @6
    wf
    #
    @17
    @10
    vn
    cZ
    cB
    cr
    @6
    wph
    vn
    cv
    #
    cZ
    wcel
    #
    @9
    cB
    cr
    wcel
    #
    mbfinf.5
    anass1rs
    #
    @6
    eqid
    #
    fmptd
    #
    cZ
    cr
    @6
    frn
    syl
    @10
    @6
    cdm
    #
    c0
    wne
    #
    @18
    @10
    cM
    @31
    wcel
    @32
    @10
    cM
    cZ
    @31
    wph
    cM
    cZ
    wcel
    @9
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
    @33
    wcel
    mbfinf.3
    cM
    uzid
    syl
    mbfinf.1
    syl6eleqr
    adantr
    @10
    vn
    @6
    cZ
    cB
    cr
    @29
    @28
    dmmptd
    eleqtrrd
    @31
    cM
    ne0i
    syl
    @31
    c0
    @7
    c0
    @6
    dm0rn0
    necon3bii
    sylib
    @10
    @23
    @19
    cB
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
    mbfinf.6
    @10
    @22
    @35
    vy
    cr
    @10
    @22
    @19
    vm
    cv
    #
    @6
    cfv
    #
    cle
    wbr
    #
    vm
    cZ
    wral
    #
    @35
    @10
    @6
    cZ
    wfn
    #
    @22
    @39
    wb
    @10
    @24
    @40
    @30
    cZ
    cr
    @6
    ffn
    syl
    #
    @21
    @38
    vz
    vm
    cZ
    @6
    @20
    @37
    @19
    cle
    breq2
    ralrn
    syl
    @39
    @19
    @25
    @6
    cfv
    #
    cle
    wbr
    #
    vn
    cZ
    wral
    @10
    @35
    @38
    @43
    vm
    vn
    cZ
    vn
    @19
    @37
    cle
    vn
    @19
    nfcv
    vn
    cle
    nfcv
    vn
    cZ
    cB
    @36
    nffvmpt1
    #
    nfbr
    @43
    vm
    nfv
    @36
    @25
    wceq
    #
    @37
    @42
    @19
    cle
    @36
    @25
    @6
    fveq2
    #
    breq2d
    cbvral
    @10
    @43
    @34
    vn
    cZ
    @10
    @26
    wa
    #
    @42
    cB
    @19
    cle
    @47
    @26
    @27
    @42
    cB
    wceq
    #
    @10
    @26
    simpr
    @28
    vn
    cZ
    cB
    cr
    @6
    @29
    fvmpt2
    syl2anc
    #
    breq2d
    ralbidva
    syl5bb
    bitrd
    rexbidv
    mpbird
    vy
    vz
    vr
    @7
    infrenegsup
    syl3anc
    @10
    @15
    @3
    @10
    cr
    @14
    @2
    clt
    @10
    @11
    @14
    wcel
    #
    @11
    @2
    wcel
    #
    wb
    #
    vr
    wal
    @14
    @2
    wceq
    @10
    @52
    vr
    @50
    @11
    cr
    wcel
    #
    @13
    wa
    #
    @10
    @51
    @13
    vr
    cr
    rabid
    @10
    @54
    @53
    @51
    wa
    @51
    @10
    @53
    @13
    @51
    @10
    @53
    wa
    #
    @37
    @12
    wceq
    #
    vm
    cZ
    wrex
    #
    @36
    @1
    cfv
    #
    @11
    wceq
    #
    vm
    cZ
    wrex
    #
    @13
    @51
    @55
    @56
    @59
    vm
    cZ
    @55
    @56
    @59
    wb
    #
    vm
    cZ
    @55
    @42
    @12
    wceq
    #
    @25
    @1
    cfv
    #
    @11
    wceq
    #
    wb
    #
    vn
    cZ
    wral
    @61
    vm
    cZ
    wral
    @55
    @65
    vn
    cZ
    @55
    @26
    wa
    #
    cB
    @12
    wceq
    #
    @0
    @11
    wceq
    #
    @62
    @64
    @66
    @67
    @11
    @0
    wceq
    #
    @68
    @66
    cB
    cc
    wcel
    #
    @11
    cc
    wcel
    @67
    @69
    wb
    @10
    @26
    @70
    @53
    @47
    cB
    @28
    recnd
    adantlr
    @66
    @11
    @10
    @53
    @26
    simplr
    recnd
    cB
    @11
    negcon2
    syl2anc
    @11
    @0
    eqcom
    syl6bb
    @66
    @42
    cB
    @12
    @10
    @26
    @48
    @53
    @49
    adantlr
    eqeq1d
    @66
    @63
    @0
    @11
    @26
    @63
    @0
    wceq
    #
    @55
    @26
    @0
    cvv
    wcel
    @71
    cB
    negex
    vn
    cZ
    @0
    cvv
    @1
    @1
    eqid
    #
    fvmpt2
    mpan2
    adantl
    eqeq1d
    3bitr4d
    ralrimiva
    @61
    @65
    vm
    vn
    cZ
    @56
    @59
    vn
    vn
    @37
    @12
    @44
    nfeq1
    vn
    @58
    @11
    vn
    cZ
    @0
    @36
    nffvmpt1
    nfeq1
    nfbi
    @65
    vm
    nfv
    @45
    @56
    @62
    @59
    @64
    @45
    @37
    @42
    @12
    @46
    eqeq1d
    @45
    @58
    @63
    @11
    @36
    @25
    @1
    fveq2
    eqeq1d
    bibi12d
    cbvral
    sylibr
    r19.21bi
    rexbidva
    @55
    @40
    @13
    @57
    wb
    @10
    @40
    @53
    @41
    adantr
    vm
    cZ
    @12
    @6
    fvelrnb
    syl
    @55
    @1
    cZ
    wfn
    #
    @51
    @60
    wb
    @55
    cZ
    cr
    @1
    wf
    #
    @73
    @10
    @74
    @53
    @10
    vn
    cZ
    @0
    cr
    @1
    @47
    cB
    @28
    renegcld
    @72
    fmptd
    #
    adantr
    cZ
    cr
    @1
    ffn
    syl
    vm
    cZ
    @11
    @1
    fvelrnb
    syl
    3bitr4d
    pm5.32da
    @10
    @51
    @53
    @10
    @2
    cr
    @11
    @10
    @74
    @2
    cr
    wss
    @75
    cZ
    cr
    @1
    frn
    syl
    sseld
    pm4.71rd
    bitr4d
    syl5bb
    alrimiv
    vr
    @14
    @2
    @13
    vr
    cr
    nfrab1
    vr
    @2
    nfcv
    cleqf
    sylibr
    supeq1d
    negeqd
    eqtrd
    mpteq2dva
    syl5eq
    wph
    vx
    cA
    @3
    cvv
    @3
    cvv
    wcel
    @10
    cr
    @2
    clt
    ltso
    supex
    a1i
    wph
    vx
    vz
    cA
    @0
    vn
    vx
    cA
    @3
    cmpt
    #
    cM
    cZ
    mbfinf.1
    @76
    eqid
    mbfinf.3
    wph
    @26
    wa
    vx
    cA
    cB
    cr
    wph
    @26
    @9
    @27
    mbfinf.5
    anassrs
    mbfinf.4
    mbfneg
    wph
    @26
    @9
    wa
    wa
    cB
    mbfinf.5
    renegcld
    @10
    @35
    @0
    @20
    cle
    wbr
    #
    vn
    cZ
    wral
    #
    vz
    cr
    wrex
    #
    vy
    cr
    mbfinf.6
    @10
    @19
    cr
    wcel
    #
    @35
    wa
    wa
    @19
    cneg
    #
    cr
    wcel
    #
    @0
    @81
    cle
    wbr
    #
    vn
    cZ
    wral
    #
    @79
    @80
    @82
    @10
    @35
    @19
    renegcl
    ad2antrl
    @10
    @80
    @35
    @84
    @10
    @80
    wa
    #
    @35
    @84
    @85
    @34
    @83
    vn
    cZ
    @85
    @26
    wa
    @19
    cB
    @10
    @80
    @26
    simplr
    @10
    @26
    @27
    @80
    @28
    adantlr
    lenegd
    ralbidva
    biimpd
    impr
    @78
    @84
    vz
    @81
    cr
    @20
    @81
    wceq
    @77
    @83
    vn
    cZ
    @20
    @81
    @0
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    rexlimddv
    mbfsup
    mbfneg
    eqeltrd
end
