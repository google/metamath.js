include "cn.mm"
include "wcel.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "crelexp.mm"
include "co.mm"
include "wss.mm"
include "cn0.mm"
include "elnn0.mm"
include "sylib.mm"
include "wi.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "oveq2.mm"
include "sseq12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "cvv.mm"
include "ssexd.mm"
include "relexp1d.mm"
include "3sstr4d.mm"
include "w3a.mm"
include "ccom.mm"
include "simp3.mm"
include "3ad2ant2.mm"
include "coss12d.mm"
include "simp1.mm"
include "relexpsucnnr.mm"
include "syl2anc.mm"
include "3exp.mm"
include "a2d.mm"
include "nnind.mm"
include "wa.mm"
include "cid.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cres.mm"
include "simpr.mm"
include "dmss.mm"
include "rnss.mm"
include "jca.mm"
include "unss12.mm"
include "3syl.mm"
include "ssres2.mm"
include "simpl.mm"
include "oveq2d.mm"
include "relexp0g.mm"
include "eqtrd.mm"
include "ex.mm"
include "jaoi.mm"
include "mpcom.mm"

theorem relexpss1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  assume relexpss1d.a: |- ( ph -> A C_ B )
  assume relexpss1d.b: |- ( ph -> B e. _V )
  assume relexpss1d.n: |- ( ph -> N e. NN0 )


  assert |- ( ph -> ( A ^r N ) C_ ( B ^r N ) )

  proof
    cN
    cn
    wcel
    #
    cN
    cc0
    wceq
    #
    wo
    #
    wph
    cA
    cN
    crelexp
    co
    #
    cB
    cN
    crelexp
    co
    #
    wss
    #
    wph
    cN
    cn0
    wcel
    @2
    relexpss1d.n
    cN
    elnn0
    sylib
    @0
    wph
    @5
    wi
    #
    @1
    wph
    cA
    vx
    cv
    #
    crelexp
    co
    #
    cB
    @7
    crelexp
    co
    #
    wss
    #
    wi
    wph
    cA
    c1
    crelexp
    co
    #
    cB
    c1
    crelexp
    co
    #
    wss
    #
    wi
    wph
    cA
    vy
    cv
    #
    crelexp
    co
    #
    cB
    @14
    crelexp
    co
    #
    wss
    #
    wi
    wph
    cA
    @14
    c1
    caddc
    co
    #
    crelexp
    co
    #
    cB
    @18
    crelexp
    co
    #
    wss
    #
    wi
    @6
    vx
    vy
    cN
    @7
    c1
    wceq
    #
    @10
    @13
    wph
    @22
    @8
    @11
    @9
    @12
    @7
    c1
    cA
    crelexp
    oveq2
    @7
    c1
    cB
    crelexp
    oveq2
    sseq12d
    imbi2d
    vx
    vy
    weq
    #
    @10
    @17
    wph
    @23
    @8
    @15
    @9
    @16
    @7
    @14
    cA
    crelexp
    oveq2
    @7
    @14
    cB
    crelexp
    oveq2
    sseq12d
    imbi2d
    @7
    @18
    wceq
    #
    @10
    @21
    wph
    @24
    @8
    @19
    @9
    @20
    @7
    @18
    cA
    crelexp
    oveq2
    @7
    @18
    cB
    crelexp
    oveq2
    sseq12d
    imbi2d
    @7
    cN
    wceq
    #
    @10
    @5
    wph
    @25
    @8
    @3
    @9
    @4
    @7
    cN
    cA
    crelexp
    oveq2
    @7
    cN
    cB
    crelexp
    oveq2
    sseq12d
    imbi2d
    wph
    cA
    cB
    @11
    @12
    relexpss1d.a
    wph
    cA
    wph
    cA
    cB
    cvv
    relexpss1d.b
    relexpss1d.a
    ssexd
    #
    relexp1d
    wph
    cB
    relexpss1d.b
    relexp1d
    3sstr4d
    @14
    cn
    wcel
    #
    wph
    @17
    @21
    @27
    wph
    @17
    @21
    @27
    wph
    @17
    w3a
    #
    @15
    cA
    ccom
    #
    @16
    cB
    ccom
    #
    @19
    @20
    @28
    @15
    @16
    cA
    cB
    @27
    wph
    @17
    simp3
    wph
    @27
    cA
    cB
    wss
    #
    @17
    relexpss1d.a
    3ad2ant2
    coss12d
    @28
    cA
    cvv
    wcel
    #
    @27
    @19
    @29
    wceq
    wph
    @27
    @32
    @17
    @26
    3ad2ant2
    @27
    wph
    @17
    simp1
    #
    cA
    @14
    cvv
    relexpsucnnr
    syl2anc
    @28
    cB
    cvv
    wcel
    #
    @27
    @20
    @30
    wceq
    wph
    @27
    @34
    @17
    relexpss1d.b
    3ad2ant2
    @33
    cB
    @14
    cvv
    relexpsucnnr
    syl2anc
    3sstr4d
    3exp
    a2d
    nnind
    @1
    wph
    @5
    @1
    wph
    wa
    #
    cid
    cA
    cdm
    #
    cA
    crn
    #
    cun
    #
    cres
    #
    cid
    cB
    cdm
    #
    cB
    crn
    #
    cun
    #
    cres
    #
    @3
    @4
    @35
    wph
    @38
    @42
    wss
    #
    @39
    @43
    wss
    @1
    wph
    simpr
    #
    wph
    @31
    @36
    @40
    wss
    #
    @37
    @41
    wss
    #
    wa
    @44
    relexpss1d.a
    @31
    @46
    @47
    cA
    cB
    dmss
    cA
    cB
    rnss
    jca
    @36
    @40
    @37
    @41
    unss12
    3syl
    @38
    @42
    cid
    ssres2
    3syl
    @35
    @3
    cA
    cc0
    crelexp
    co
    #
    @39
    @35
    cN
    cc0
    cA
    crelexp
    @1
    wph
    simpl
    #
    oveq2d
    @35
    wph
    @32
    @48
    @39
    wceq
    @45
    @26
    cA
    cvv
    relexp0g
    3syl
    eqtrd
    @35
    @4
    cB
    cc0
    crelexp
    co
    #
    @43
    @35
    cN
    cc0
    cB
    crelexp
    @49
    oveq2d
    @35
    wph
    @34
    @50
    @43
    wceq
    @45
    relexpss1d.b
    cB
    cvv
    relexp0g
    3syl
    eqtrd
    3sstr4d
    ex
    jaoi
    mpcom
end
