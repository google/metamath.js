include "csn.mm"
include "cxp.mm"
include "wf1.mm"
include "wfo.mm"
include "wa.mm"
include "wf1o.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "cop.mm"
include "wcel.mm"
include "snidg.mm"
include "syl.mm"
include "adantr.mm"
include "simpr.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "cmpt.mm"
include "opeq2.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "fmptd.mm"
include "w3a.mm"
include "simpl1.mm"
include "cvv.mm"
include "elexd.mm"
include "fvmpt2.mm"
include "eqcomd.mm"
include "3adant3.mm"
include "a1i.mm"
include "adantl.mm"
include "opex.mm"
include "fvmptd.mm"
include "3adant2.mm"
include "3eqtrd.mm"
include "wb.mm"
include "vex.mm"
include "opthg2.mm"
include "mpbid.mm"
include "simprd.mm"
include "ex.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "jca.mm"
include "dff13.mm"
include "sylibr.mm"
include "wrex.mm"
include "elsnxp.mm"
include "id.mm"
include "eqtr2d.mm"
include "adantlr.mm"
include "reximdva.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "dffo3.mm"
include "df-f1o.mm"

theorem projf1o
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let vy: setvar y
  let vz: setvar z
  assume projf1o.1: |- ( ph -> A e. V )
  assume projf1o.2: |- F = ( x e. B |-> <. A , x >. )

  disjoint A x
  disjoint B x
  disjoint A y
  disjoint x y
  disjoint A z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint F y
  disjoint F z
  disjoint V y
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> F : B -1-1-onto-> ( { A } X. B ) )

  proof
    wph
    cB
    cA
    csn
    #
    cB
    cxp
    #
    cF
    wf1
    #
    cB
    @1
    cF
    wfo
    #
    wa
    cB
    @1
    cF
    wf1o
    wph
    @2
    @3
    wph
    cB
    @1
    cF
    wf
    #
    vy
    cv
    #
    cF
    cfv
    #
    vz
    cv
    #
    cF
    cfv
    #
    wceq
    #
    @5
    @7
    wceq
    #
    wi
    #
    vz
    cB
    wral
    vy
    cB
    wral
    #
    wa
    @2
    wph
    @4
    @12
    wph
    vy
    cB
    cA
    @5
    cop
    #
    @1
    cF
    wph
    @5
    cB
    wcel
    #
    wa
    #
    cA
    @0
    wcel
    #
    @14
    @13
    @1
    wcel
    wph
    @16
    @14
    wph
    cA
    cV
    wcel
    #
    @16
    projf1o.1
    cA
    cV
    snidg
    syl
    adantr
    wph
    @14
    simpr
    #
    cA
    @5
    @0
    cB
    opelxpi
    syl2anc
    #
    cF
    vx
    cB
    cA
    vx
    cv
    #
    cop
    #
    cmpt
    vy
    cB
    @13
    cmpt
    #
    projf1o.2
    vx
    vy
    cB
    @21
    @13
    @20
    @5
    cA
    opeq2
    cbvmptv
    eqtri
    #
    fmptd
    #
    wph
    @11
    vy
    vz
    cB
    cB
    wph
    @14
    @7
    cB
    wcel
    #
    @11
    wph
    @14
    @25
    w3a
    #
    @9
    @10
    @26
    @9
    wa
    #
    wph
    @13
    cA
    @7
    cop
    #
    wceq
    #
    @10
    wph
    @14
    @25
    @9
    simpl1
    @27
    @13
    @6
    @8
    @28
    @26
    @13
    @6
    wceq
    #
    @9
    wph
    @14
    @30
    @25
    @15
    @6
    @13
    @15
    @14
    @13
    cvv
    wcel
    @6
    @13
    wceq
    #
    @18
    @15
    @13
    @1
    @19
    elexd
    vy
    cB
    @13
    cvv
    cF
    @23
    fvmpt2
    syl2anc
    #
    eqcomd
    3adant3
    adantr
    @26
    @9
    simpr
    @26
    @8
    @28
    wceq
    #
    @9
    wph
    @25
    @33
    @14
    wph
    @25
    wa
    #
    vy
    @7
    @13
    @28
    cB
    cF
    cvv
    cF
    @22
    wceq
    @34
    @23
    a1i
    @10
    @29
    @34
    @5
    @7
    cA
    opeq2
    adantl
    wph
    @25
    simpr
    @28
    cvv
    wcel
    @34
    cA
    @7
    opex
    a1i
    fvmptd
    3adant2
    adantr
    3eqtrd
    wph
    @29
    wa
    #
    cA
    cA
    wceq
    #
    @10
    @35
    @29
    @36
    @10
    wa
    #
    wph
    @29
    simpr
    wph
    @29
    @37
    wb
    #
    @29
    wph
    @17
    @7
    cvv
    wcel
    #
    @38
    projf1o.1
    @39
    wph
    vz
    vex
    a1i
    cA
    @5
    cA
    @7
    cV
    cvv
    opthg2
    syl2anc
    adantr
    mpbid
    simprd
    syl2anc
    ex
    3expb
    ralrimivva
    jca
    vy
    vz
    cB
    @1
    cF
    dff13
    sylibr
    wph
    @4
    @7
    @6
    wceq
    #
    vy
    cB
    wrex
    #
    vz
    @1
    wral
    #
    wa
    @3
    wph
    @4
    @42
    @24
    wph
    @41
    vz
    @1
    wph
    @7
    @1
    wcel
    #
    wa
    #
    @7
    @13
    wceq
    #
    vy
    cB
    wrex
    #
    @41
    @44
    @43
    @46
    wph
    @43
    simpr
    wph
    @43
    @46
    wb
    #
    @43
    wph
    @17
    @47
    projf1o.1
    vy
    cB
    cV
    cA
    @7
    elsnxp
    syl
    adantr
    mpbid
    @44
    @45
    @40
    vy
    cB
    wph
    @14
    @45
    @40
    wi
    @43
    @15
    @45
    @40
    @15
    @45
    wa
    @6
    @13
    @7
    @15
    @31
    @45
    @32
    adantr
    @45
    @13
    @7
    wceq
    @15
    @45
    @7
    @13
    @45
    id
    eqcomd
    adantl
    eqtr2d
    ex
    adantlr
    reximdva
    mpd
    ralrimiva
    jca
    vy
    vz
    cB
    @1
    cF
    dffo3
    sylibr
    jca
    cB
    @1
    cF
    df-f1o
    sylibr
end
