include "cin.mm"
include "cixp.mm"
include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "cres.mm"
include "cmpt.mm"
include "wf1.mm"
include "wral.mm"
include "wss.mm"
include "inss2.mm"
include "ssfi.mm"
include "sylancl.mm"
include "inss1.mm"
include "ralrimiva.mm"
include "ssralv.mm"
include "mpsyl.mm"
include "ixpfi.mm"
include "syl2anc.mm"
include "wi.mm"
include "resixp.mm"
include "mpan.mm"
include "a1i.mm"
include "wa.mm"
include "wceq.mm"
include "wb.mm"
include "cfv.mm"
include "cdif.mm"
include "wfn.mm"
include "simprl.mm"
include "vex.mm"
include "elixp.mm"
include "sylib.mm"
include "simprd.mm"
include "simprr.mm"
include "r19.26.mm"
include "difss.mm"
include "ax-mp.mm"
include "csn.mm"
include "sseld.mm"
include "elsni.mm"
include "syl6.mm"
include "anim12d.mm"
include "eqtr3.mm"
include "ralimdva.mm"
include "adantr.mm"
include "syl5.mm"
include "syl5bir.mm"
include "mp2and.mm"
include "biantrud.mm"
include "fvres.mm"
include "eqeq12d.mm"
include "ralbiia.mm"
include "cun.mm"
include "inundif.mm"
include "raleqi.mm"
include "ralunb.mm"
include "bitr3i.mm"
include "3bitr4g.mm"
include "simpld.mm"
include "fnssres.mm"
include "eqfnfv.mm"
include "3bitr4d.mm"
include "ex.mm"
include "dom2lem.mm"
include "f1fi.mm"

theorem ixpfi2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vf: setvar f
  let vg: setvar g
  assume ixpfi2.1: |- ( ph -> C e. Fin )
  assume ixpfi2.2: |- ( ( ph /\ x e. A ) -> B e. Fin )
  assume ixpfi2.3: |- ( ( ph /\ x e. ( A \ C ) ) -> B C_ { D } )

  disjoint A x
  disjoint C x
  disjoint ph x
  disjoint f g
  disjoint f x
  disjoint A f
  disjoint g x
  disjoint A g
  disjoint B f
  disjoint B g
  disjoint C f
  disjoint C g
  disjoint f ph
  disjoint g ph
  assert |- ( ph -> X_ x e. A B e. Fin )

  proof
    wph
    vx
    cA
    cC
    cin
    #
    cB
    cixp
    #
    cfn
    wcel
    #
    vx
    cA
    cB
    cixp
    #
    @1
    vf
    @3
    vf
    cv
    #
    @0
    cres
    #
    cmpt
    #
    wf1
    @3
    cfn
    wcel
    wph
    @0
    cfn
    wcel
    #
    cB
    cfn
    wcel
    #
    vx
    @0
    wral
    #
    @2
    wph
    cC
    cfn
    wcel
    @0
    cC
    wss
    @7
    ixpfi2.1
    cA
    cC
    inss2
    cC
    @0
    ssfi
    sylancl
    @0
    cA
    wss
    #
    wph
    @8
    vx
    cA
    wral
    @9
    cA
    cC
    inss1
    #
    wph
    @8
    vx
    cA
    ixpfi2.2
    ralrimiva
    @8
    vx
    @0
    cA
    ssralv
    mpsyl
    vx
    @0
    cB
    ixpfi
    syl2anc
    wph
    vf
    vg
    @3
    @1
    @5
    vg
    cv
    #
    @0
    cres
    #
    @4
    @3
    wcel
    #
    @5
    @1
    wcel
    #
    wi
    wph
    @10
    @14
    @15
    @11
    vx
    cA
    @0
    cB
    @4
    resixp
    mpan
    a1i
    wph
    @14
    @12
    @3
    wcel
    #
    wa
    #
    @5
    @13
    wceq
    #
    @4
    @12
    wceq
    #
    wb
    wph
    @17
    wa
    #
    vx
    cv
    #
    @5
    cfv
    #
    @21
    @13
    cfv
    #
    wceq
    #
    vx
    @0
    wral
    #
    @21
    @4
    cfv
    #
    @21
    @12
    cfv
    #
    wceq
    #
    vx
    cA
    wral
    #
    @18
    @19
    @20
    @28
    vx
    @0
    wral
    #
    @30
    @28
    vx
    cA
    cC
    cdif
    #
    wral
    #
    wa
    #
    @25
    @29
    @20
    @32
    @30
    @20
    @26
    cB
    wcel
    #
    vx
    cA
    wral
    #
    @27
    cB
    wcel
    #
    vx
    cA
    wral
    #
    @32
    @20
    @4
    cA
    wfn
    #
    @35
    @20
    @14
    @38
    @35
    wa
    wph
    @14
    @16
    simprl
    vx
    cA
    cB
    @4
    vf
    vex
    elixp
    sylib
    #
    simprd
    @20
    @12
    cA
    wfn
    #
    @37
    @20
    @16
    @40
    @37
    wa
    wph
    @14
    @16
    simprr
    vx
    cA
    cB
    @12
    vg
    vex
    elixp
    sylib
    #
    simprd
    @35
    @37
    wa
    @34
    @36
    wa
    #
    vx
    cA
    wral
    #
    @20
    @32
    @34
    @36
    vx
    cA
    r19.26
    @43
    @42
    vx
    @31
    wral
    #
    @20
    @32
    @31
    cA
    wss
    @43
    @44
    wi
    cA
    cC
    difss
    @42
    vx
    @31
    cA
    ssralv
    ax-mp
    wph
    @44
    @32
    wi
    @17
    wph
    @42
    @28
    vx
    @31
    wph
    @21
    @31
    wcel
    wa
    #
    @42
    @26
    cD
    wceq
    #
    @27
    cD
    wceq
    #
    wa
    @28
    @45
    @34
    @46
    @36
    @47
    @45
    @34
    @26
    cD
    csn
    #
    wcel
    @46
    @45
    cB
    @48
    @26
    ixpfi2.3
    sseld
    @26
    cD
    elsni
    syl6
    @45
    @36
    @27
    @48
    wcel
    @47
    @45
    cB
    @48
    @27
    ixpfi2.3
    sseld
    @27
    cD
    elsni
    syl6
    anim12d
    @26
    @27
    cD
    eqtr3
    syl6
    ralimdva
    adantr
    syl5
    syl5bir
    mp2and
    biantrud
    @24
    @28
    vx
    @0
    @21
    @0
    wcel
    @22
    @26
    @23
    @27
    @21
    @0
    @4
    fvres
    @21
    @0
    @12
    fvres
    eqeq12d
    ralbiia
    @29
    @28
    vx
    @0
    @31
    cun
    #
    wral
    @33
    @28
    vx
    @49
    cA
    cA
    cC
    inundif
    raleqi
    @28
    vx
    @0
    @31
    ralunb
    bitr3i
    3bitr4g
    @20
    @5
    @0
    wfn
    #
    @13
    @0
    wfn
    #
    @18
    @25
    wb
    @20
    @38
    @10
    @50
    @20
    @38
    @35
    @39
    simpld
    #
    @11
    cA
    @0
    @4
    fnssres
    sylancl
    @20
    @40
    @10
    @51
    @20
    @40
    @37
    @41
    simpld
    #
    @11
    cA
    @0
    @12
    fnssres
    sylancl
    vx
    @0
    @5
    @13
    eqfnfv
    syl2anc
    @20
    @38
    @40
    @19
    @29
    wb
    @52
    @53
    vx
    cA
    @4
    @12
    eqfnfv
    syl2anc
    3bitr4d
    ex
    dom2lem
    @3
    @1
    @6
    f1fi
    syl2anc
end
