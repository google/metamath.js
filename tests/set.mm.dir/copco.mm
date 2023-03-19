include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "cv.mm"
include "c2.mm"
include "cdiv.mm"
include "cle.mm"
include "wbr.mm"
include "cmul.mm"
include "ccom.mm"
include "cfv.mm"
include "cmin.mm"
include "cif.mm"
include "cmpt.mm"
include "cpco.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cuni.mm"
include "wf.mm"
include "cii.mm"
include "ccn.mm"
include "iiuni.mm"
include "eqid.mm"
include "cnf.mm"
include "syl.mm"
include "elii1.mm"
include "iihalf1.mm"
include "sylbir.mm"
include "fvco3.mm"
include "syl2an.mm"
include "anassrs.mm"
include "ifeq1da.mm"
include "wn.mm"
include "elii2.mm"
include "iihalf2.mm"
include "ifeq2da.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "cnco.mm"
include "syl2anc.mm"
include "pcoval.mm"
include "wral.mm"
include "pcocn.mm"
include "eqeltrrd.mm"
include "fmpt.mm"
include "sylibr.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "fvif.mm"
include "syl6eq.mm"
include "fmptcof.mm"
include "3eqtr4rd.mm"

theorem copco
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cX: class X
  let vj: setvar j
  assume pcoval.2: |- ( ph -> F e. ( II Cn J ) )
  assume pcoval.3: |- ( ph -> G e. ( II Cn J ) )
  assume pcoval2.4: |- ( ph -> ( F ` 1 ) = ( G ` 0 ) )
  assume copco.6: |- ( ph -> H e. ( J Cn K ) )


  assert |- ( ph -> ( H o. ( F ( *p ` J ) G ) ) = ( ( H o. F ) ( *p ` K ) ( H o. G ) ) )

  proof
    wph
    vx
    cc0
    c1
    cicc
    co
    #
    vx
    cv
    #
    c1
    c2
    cdiv
    co
    #
    cle
    wbr
    #
    c2
    @1
    cmul
    co
    #
    cH
    cF
    ccom
    #
    cfv
    #
    @4
    c1
    cmin
    co
    #
    cH
    cG
    ccom
    #
    cfv
    #
    cif
    #
    cmpt
    vx
    @0
    @3
    @4
    cF
    cfv
    #
    cH
    cfv
    #
    @7
    cG
    cfv
    #
    cH
    cfv
    #
    cif
    #
    cmpt
    @5
    @8
    cK
    cpco
    cfv
    co
    cH
    cF
    cG
    cJ
    cpco
    cfv
    co
    #
    ccom
    wph
    vx
    @0
    @10
    @15
    wph
    @1
    @0
    wcel
    #
    wa
    #
    @10
    @3
    @12
    @9
    cif
    @15
    @18
    @3
    @6
    @12
    @9
    wph
    @17
    @3
    @6
    @12
    wceq
    #
    wph
    @0
    cJ
    cuni
    #
    cF
    wf
    #
    @4
    @0
    wcel
    #
    @19
    @17
    @3
    wa
    #
    wph
    cF
    cii
    cJ
    ccn
    co
    #
    wcel
    #
    @21
    pcoval.2
    cF
    cii
    cJ
    @0
    @20
    iiuni
    @20
    eqid
    #
    cnf
    syl
    @23
    @1
    cc0
    @2
    cicc
    co
    wcel
    @22
    @1
    elii1
    @1
    iihalf1
    sylbir
    @0
    @20
    @4
    cH
    cF
    fvco3
    syl2an
    anassrs
    ifeq1da
    @18
    @3
    @9
    @14
    @12
    wph
    @17
    @3
    wn
    #
    @9
    @14
    wceq
    #
    wph
    @0
    @20
    cG
    wf
    #
    @7
    @0
    wcel
    #
    @28
    @17
    @27
    wa
    #
    wph
    cG
    @24
    wcel
    #
    @29
    pcoval.3
    cG
    cii
    cJ
    @0
    @20
    iiuni
    @26
    cnf
    syl
    @31
    @1
    @2
    c1
    cicc
    co
    wcel
    @30
    @1
    elii2
    @1
    iihalf2
    syl
    @0
    @20
    @7
    cH
    cG
    fvco3
    syl2an
    anassrs
    ifeq2da
    eqtrd
    mpteq2dva
    wph
    vx
    @5
    @8
    cK
    wph
    @25
    cH
    cJ
    cK
    ccn
    co
    wcel
    #
    @5
    cii
    cK
    ccn
    co
    #
    wcel
    pcoval.2
    copco.6
    cF
    cH
    cii
    cJ
    cK
    cnco
    syl2anc
    wph
    @32
    @33
    @8
    @34
    wcel
    pcoval.3
    copco.6
    cG
    cH
    cii
    cJ
    cK
    cnco
    syl2anc
    pcoval
    wph
    vx
    vy
    @0
    @20
    @3
    @11
    @13
    cif
    #
    vy
    cv
    #
    cH
    cfv
    #
    @15
    @16
    cH
    wph
    @0
    @20
    vx
    @0
    @35
    cmpt
    #
    wf
    #
    @35
    @20
    wcel
    vx
    @0
    wral
    wph
    @38
    @24
    wcel
    @39
    wph
    @16
    @38
    @24
    wph
    vx
    cF
    cG
    cJ
    pcoval.2
    pcoval.3
    pcoval
    #
    wph
    cF
    cG
    cJ
    pcoval.2
    pcoval.3
    pcoval2.4
    pcocn
    eqeltrrd
    @38
    cii
    cJ
    @0
    @20
    iiuni
    @26
    cnf
    syl
    vx
    @0
    @20
    @35
    @38
    @38
    eqid
    fmpt
    sylibr
    @40
    wph
    vy
    @20
    cK
    cuni
    #
    cH
    wph
    @33
    @20
    @41
    cH
    wf
    copco.6
    cH
    cJ
    cK
    @20
    @41
    @26
    @41
    eqid
    cnf
    syl
    feqmptd
    @36
    @35
    wceq
    @37
    @35
    cH
    cfv
    @15
    @36
    @35
    cH
    fveq2
    @3
    @11
    @13
    cH
    fvif
    syl6eq
    fmptcof
    3eqtr4rd
end
