include "cmpt.mm"
include "cmbf.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cneg.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "nfcv.mm"
include "nffvmpt1.mm"
include "nfbr.mm"
include "nfif.mm"
include "fveq2.mm"
include "breq2d.mm"
include "ifbieq1d.mm"
include "cbvmpt.mm"
include "cr.mm"
include "simpr.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "mpteq2dva.mm"
include "syl5eq.mm"
include "adantr.mm"
include "wf.mm"
include "fmptd.mm"
include "ffvelrnda.mm"
include "eleq1d.mm"
include "biimpar.mm"
include "mbfpos.mm"
include "eqeltrrd.mm"
include "nfneg.mm"
include "negeqd.mm"
include "renegcld.mm"
include "mbfneg.mm"
include "jca.mm"
include "adantlr.mm"
include "simprl.mm"
include "eqeltrd.mm"
include "simprr.mm"
include "mbfposr.mm"
include "impbida.mm"

theorem mbfposb
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume mbfpos.1: |- ( ( ph /\ x e. A ) -> B e. RR )

  disjoint A x
  disjoint ph x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint ph y
  assert |- ( ph -> ( ( x e. A |-> B ) e. MblFn <-> ( ( x e. A |-> if ( 0 <_ B , B , 0 ) ) e. MblFn /\ ( x e. A |-> if ( 0 <_ -u B , -u B , 0 ) ) e. MblFn ) ) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    cmbf
    wcel
    #
    vx
    cA
    cc0
    cB
    cle
    wbr
    #
    cB
    cc0
    cif
    #
    cmpt
    #
    cmbf
    wcel
    #
    vx
    cA
    cc0
    cB
    cneg
    #
    cle
    wbr
    #
    @6
    cc0
    cif
    #
    cmpt
    #
    cmbf
    wcel
    #
    wa
    #
    wph
    @1
    wa
    #
    @5
    @10
    @12
    vy
    cA
    cc0
    vy
    cv
    #
    @0
    cfv
    #
    cle
    wbr
    #
    @14
    cc0
    cif
    #
    cmpt
    #
    @4
    cmbf
    wph
    @17
    @4
    wceq
    #
    @1
    wph
    @17
    vx
    cA
    cc0
    vx
    cv
    #
    @0
    cfv
    #
    cle
    wbr
    #
    @20
    cc0
    cif
    #
    cmpt
    @4
    vy
    vx
    cA
    @16
    @22
    @15
    vx
    @14
    cc0
    vx
    cc0
    @14
    cle
    vx
    cc0
    nfcv
    #
    vx
    cle
    nfcv
    #
    vx
    cA
    cB
    @13
    nffvmpt1
    #
    nfbr
    @25
    @23
    nfif
    vy
    @22
    nfcv
    @13
    @19
    wceq
    #
    @15
    @21
    @14
    @20
    cc0
    @26
    @14
    @20
    cc0
    cle
    @13
    @19
    @0
    fveq2
    #
    breq2d
    @27
    ifbieq1d
    cbvmpt
    wph
    vx
    cA
    @22
    @3
    wph
    @19
    cA
    wcel
    #
    wa
    #
    @21
    @2
    @20
    cB
    cc0
    @29
    @20
    cB
    cc0
    cle
    @29
    @28
    cB
    cr
    wcel
    @20
    cB
    wceq
    wph
    @28
    simpr
    mbfpos.1
    vx
    cA
    cB
    cr
    @0
    @0
    eqid
    #
    fvmpt2
    syl2anc
    #
    breq2d
    @31
    ifbieq1d
    mpteq2dva
    syl5eq
    #
    adantr
    @12
    vy
    cA
    @14
    @12
    cA
    cr
    @13
    @0
    wph
    cA
    cr
    @0
    wf
    @1
    wph
    vx
    cA
    cB
    cr
    @0
    mbfpos.1
    @30
    fmptd
    #
    adantr
    ffvelrnda
    #
    wph
    vy
    cA
    @14
    cmpt
    #
    cmbf
    wcel
    @1
    wph
    @35
    @0
    cmbf
    wph
    @35
    vx
    cA
    @20
    cmpt
    @0
    vy
    vx
    cA
    @14
    @20
    @25
    vy
    @20
    nfcv
    @27
    cbvmpt
    wph
    vx
    cA
    @20
    cB
    @31
    mpteq2dva
    syl5eq
    #
    eleq1d
    biimpar
    #
    mbfpos
    eqeltrrd
    @12
    vy
    cA
    cc0
    @14
    cneg
    #
    cle
    wbr
    #
    @38
    cc0
    cif
    #
    cmpt
    #
    @9
    cmbf
    wph
    @41
    @9
    wceq
    #
    @1
    wph
    @41
    vx
    cA
    cc0
    @20
    cneg
    #
    cle
    wbr
    #
    @43
    cc0
    cif
    #
    cmpt
    @9
    vy
    vx
    cA
    @40
    @45
    @39
    vx
    @38
    cc0
    vx
    cc0
    @38
    cle
    @23
    @24
    vx
    @14
    @25
    nfneg
    #
    nfbr
    @46
    @23
    nfif
    vy
    @45
    nfcv
    @26
    @39
    @44
    @38
    @43
    cc0
    @26
    @38
    @43
    cc0
    cle
    @26
    @14
    @20
    @27
    negeqd
    #
    breq2d
    @47
    ifbieq1d
    cbvmpt
    wph
    vx
    cA
    @45
    @8
    @29
    @44
    @7
    @43
    @6
    cc0
    @29
    @43
    @6
    cc0
    cle
    @29
    @20
    cB
    @31
    negeqd
    #
    breq2d
    @48
    ifbieq1d
    mpteq2dva
    syl5eq
    #
    adantr
    @12
    vy
    cA
    @38
    @12
    @13
    cA
    wcel
    #
    wa
    @14
    @34
    renegcld
    @12
    vy
    cA
    @14
    cr
    @34
    @37
    mbfneg
    mbfpos
    eqeltrrd
    jca
    wph
    @11
    wa
    #
    @35
    @0
    cmbf
    wph
    @35
    @0
    wceq
    @11
    @36
    adantr
    @51
    vy
    cA
    @14
    wph
    @50
    @14
    cr
    wcel
    @11
    wph
    cA
    cr
    @13
    @0
    @33
    ffvelrnda
    adantlr
    @51
    @17
    @4
    cmbf
    wph
    @18
    @11
    @32
    adantr
    wph
    @5
    @10
    simprl
    eqeltrd
    @51
    @41
    @9
    cmbf
    wph
    @42
    @11
    @49
    adantr
    wph
    @5
    @10
    simprr
    eqeltrd
    mbfposr
    eqeltrrd
    impbida
end
