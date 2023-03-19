include "cmpt.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cioo.mm"
include "crn.mm"
include "wral.mm"
include "cmbf.mm"
include "wa.mm"
include "cin.mm"
include "cdif.mm"
include "cun.mm"
include "inundif.mm"
include "incom.mm"
include "dfin4.mm"
include "eqtri.mm"
include "id.mm"
include "cr.mm"
include "wss.mm"
include "covol.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "wn.mm"
include "cab.mm"
include "symdif2.mm"
include "eldif.mm"
include "eldifi.mm"
include "adantl.mm"
include "sylan2.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "3eqtr4d.mm"
include "ralrimiva.mm"
include "nfv.mm"
include "nffvmpt1.mm"
include "nfeq.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "cbvral.mm"
include "sylib.mm"
include "r19.21bi.mm"
include "eleq1d.mm"
include "sylan2br.mm"
include "anass1rs.mm"
include "pm5.32da.mm"
include "wfn.mm"
include "wf.mm"
include "fmptd.mm"
include "ffn.mm"
include "syl.mm"
include "adantr.mm"
include "elpreima.mm"
include "3bitr4d.mm"
include "ex.mm"
include "con1d.mm"
include "abssdv.mm"
include "syl5eqss.mm"
include "unssad.mm"
include "sstrd.mm"
include "ovolssnul.mm"
include "syl3anc.mm"
include "nulmbl.mm"
include "difmbl.mm"
include "syl2anr.mm"
include "syl5eqel.mm"
include "unssbd.mm"
include "unmbl.mm"
include "syl5eqelr.mm"
include "impbida.mm"
include "ralbidv.mm"
include "ismbf.mm"

theorem mbfeqalem
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vz: setvar z
  let vy: setvar y
  assume mbfeqa.1: |- ( ph -> A C_ RR )
  assume mbfeqa.2: |- ( ph -> ( vol* ` A ) = 0 )
  assume mbfeqa.3: |- ( ( ph /\ x e. ( B \ A ) ) -> C = D )
  assume mbfeqalem.4: |- ( ( ph /\ x e. B ) -> C e. RR )
  assume mbfeqalem.5: |- ( ( ph /\ x e. B ) -> D e. RR )

  disjoint A x
  disjoint B x
  disjoint ph x
  disjoint x z
  disjoint A z
  disjoint x y
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C y
  disjoint C z
  disjoint D y
  disjoint D z
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( ( x e. B |-> C ) e. MblFn <-> ( x e. B |-> D ) e. MblFn ) )

  proof
    wph
    vx
    cB
    cC
    cmpt
    #
    ccnv
    vy
    cv
    #
    cima
    #
    cvol
    cdm
    #
    wcel
    #
    vy
    cioo
    crn
    #
    wral
    #
    vx
    cB
    cD
    cmpt
    #
    ccnv
    @1
    cima
    #
    @3
    wcel
    #
    vy
    @5
    wral
    #
    @0
    cmbf
    wcel
    #
    @7
    cmbf
    wcel
    #
    wph
    @4
    @9
    vy
    @5
    wph
    @4
    @9
    wph
    @4
    wa
    #
    @8
    @8
    @2
    cin
    #
    @8
    @2
    cdif
    #
    cun
    #
    @3
    @8
    @2
    inundif
    @13
    @14
    @3
    wcel
    @15
    @3
    wcel
    #
    @16
    @3
    wcel
    @13
    @14
    @2
    @2
    @8
    cdif
    #
    cdif
    #
    @3
    @14
    @2
    @8
    cin
    #
    @19
    @8
    @2
    incom
    @2
    @8
    dfin4
    eqtri
    @4
    @4
    @18
    @3
    wcel
    #
    @19
    @3
    wcel
    wph
    @4
    id
    wph
    @18
    cr
    wss
    @18
    covol
    cfv
    cc0
    wceq
    #
    @21
    wph
    @18
    cA
    cr
    wph
    @18
    @15
    cA
    wph
    @18
    @15
    cun
    vz
    cv
    #
    @2
    wcel
    #
    @23
    @8
    wcel
    #
    wb
    #
    wn
    #
    vz
    cab
    cA
    vz
    @2
    @8
    symdif2
    wph
    @27
    vz
    cA
    wph
    @23
    cA
    wcel
    #
    @26
    wph
    @28
    wn
    #
    @26
    wph
    @29
    wa
    #
    @23
    cB
    wcel
    #
    @23
    @0
    cfv
    #
    @1
    wcel
    #
    wa
    #
    @31
    @23
    @7
    cfv
    #
    @1
    wcel
    #
    wa
    #
    @24
    @25
    @30
    @31
    @33
    @36
    wph
    @31
    @29
    @33
    @36
    wb
    #
    @31
    @29
    wa
    wph
    @23
    cB
    cA
    cdif
    #
    wcel
    #
    @38
    @23
    cB
    cA
    eldif
    wph
    @40
    wa
    @32
    @35
    @1
    wph
    @32
    @35
    wceq
    #
    vz
    @39
    wph
    vx
    cv
    #
    @0
    cfv
    #
    @42
    @7
    cfv
    #
    wceq
    #
    vx
    @39
    wral
    @41
    vz
    @39
    wral
    wph
    @45
    vx
    @39
    wph
    @42
    @39
    wcel
    #
    wa
    #
    cC
    cD
    @43
    @44
    mbfeqa.3
    @47
    @42
    cB
    wcel
    #
    cC
    cr
    wcel
    #
    @43
    cC
    wceq
    @46
    @48
    wph
    @42
    cB
    cA
    eldifi
    #
    adantl
    #
    @46
    wph
    @48
    @49
    @50
    mbfeqalem.4
    sylan2
    vx
    cB
    cC
    cr
    @0
    @0
    eqid
    #
    fvmpt2
    syl2anc
    @47
    @48
    cD
    cr
    wcel
    #
    @44
    cD
    wceq
    @51
    @46
    wph
    @48
    @53
    @50
    mbfeqalem.5
    sylan2
    vx
    cB
    cD
    cr
    @7
    @7
    eqid
    #
    fvmpt2
    syl2anc
    3eqtr4d
    ralrimiva
    @45
    @41
    vx
    vz
    @39
    @45
    vz
    nfv
    vx
    @32
    @35
    vx
    cB
    cC
    @23
    nffvmpt1
    vx
    cB
    cD
    @23
    nffvmpt1
    nfeq
    @42
    @23
    wceq
    @43
    @32
    @44
    @35
    @42
    @23
    @0
    fveq2
    @42
    @23
    @7
    fveq2
    eqeq12d
    cbvral
    sylib
    r19.21bi
    eleq1d
    sylan2br
    anass1rs
    pm5.32da
    @30
    @0
    cB
    wfn
    #
    @24
    @34
    wb
    wph
    @55
    @29
    wph
    cB
    cr
    @0
    wf
    #
    @55
    wph
    vx
    cB
    cC
    cr
    @0
    mbfeqalem.4
    @52
    fmptd
    #
    cB
    cr
    @0
    ffn
    syl
    adantr
    cB
    @23
    @1
    @0
    elpreima
    syl
    @30
    @7
    cB
    wfn
    #
    @25
    @37
    wb
    wph
    @58
    @29
    wph
    cB
    cr
    @7
    wf
    #
    @58
    wph
    vx
    cB
    cD
    cr
    @7
    mbfeqalem.5
    @54
    fmptd
    #
    cB
    cr
    @7
    ffn
    syl
    adantr
    cB
    @23
    @1
    @7
    elpreima
    syl
    3bitr4d
    ex
    con1d
    abssdv
    syl5eqss
    #
    unssad
    #
    mbfeqa.1
    sstrd
    wph
    @18
    cA
    wss
    cA
    cr
    wss
    #
    cA
    covol
    cfv
    cc0
    wceq
    #
    @22
    @62
    mbfeqa.1
    mbfeqa.2
    @18
    cA
    ovolssnul
    syl3anc
    @18
    nulmbl
    syl2anc
    #
    @2
    @18
    difmbl
    syl2anr
    syl5eqel
    wph
    @17
    @4
    wph
    @15
    cr
    wss
    @15
    covol
    cfv
    cc0
    wceq
    #
    @17
    wph
    @15
    cA
    cr
    wph
    @18
    @15
    cA
    @61
    unssbd
    #
    mbfeqa.1
    sstrd
    wph
    @15
    cA
    wss
    @63
    @64
    @66
    @67
    mbfeqa.1
    mbfeqa.2
    @15
    cA
    ovolssnul
    syl3anc
    @15
    nulmbl
    syl2anc
    #
    adantr
    @14
    @15
    unmbl
    syl2anc
    syl5eqelr
    wph
    @9
    wa
    #
    @2
    @20
    @18
    cun
    #
    @3
    @2
    @8
    inundif
    @69
    @20
    @3
    wcel
    @21
    @70
    @3
    wcel
    @69
    @20
    @8
    @15
    cdif
    #
    @3
    @20
    @14
    @71
    @2
    @8
    incom
    @8
    @2
    dfin4
    eqtri
    @9
    @9
    @17
    @71
    @3
    wcel
    wph
    @9
    id
    @68
    @8
    @15
    difmbl
    syl2anr
    syl5eqel
    wph
    @21
    @9
    @65
    adantr
    @20
    @18
    unmbl
    syl2anc
    syl5eqelr
    impbida
    ralbidv
    wph
    @56
    @11
    @6
    wb
    @57
    vy
    cB
    @0
    ismbf
    syl
    wph
    @59
    @12
    @10
    wb
    @60
    vy
    cB
    @7
    ismbf
    syl
    3bitr4d
end
