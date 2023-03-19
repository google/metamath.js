include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "ccnp.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "cfcls.mm"
include "cfcf.mm"
include "wi.mm"
include "cfil.mm"
include "wral.mm"
include "wa.mm"
include "cnpf2.mm"
include "3expa.mm"
include "3adantl3.mm"
include "ctop.mm"
include "topontop.mm"
include "cnpfcfi.mm"
include "3com23.mm"
include "3expia.mm"
include "sylan.mm"
include "ralrimivw.mm"
include "3ad2antl2.mm"
include "jca.mm"
include "ex.mm"
include "cflim.mm"
include "cflf.mm"
include "cfm.mm"
include "wss.mm"
include "wceq.mm"
include "wrex.mm"
include "cfbas.mm"
include "simplrl.mm"
include "filfbas.mm"
include "syl.mm"
include "simprl.mm"
include "simpllr.mm"
include "simprr.mm"
include "fmfnfm.mm"
include "r19.29.mm"
include "flimfcls.mm"
include "simpll1.mm"
include "ad2antrr.mm"
include "simprrl.mm"
include "flimss2.mm"
include "syl3anc.mm"
include "sseldd.mm"
include "sseldi.mm"
include "simpll2.mm"
include "simplr.mm"
include "fcfval.mm"
include "simprrr.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "eleq2d.mm"
include "biimpd.mm"
include "embantd.mm"
include "expr.mm"
include "com23.mm"
include "impd.mm"
include "rexlimdva.mm"
include "syl5.mm"
include "mpan2d.mm"
include "ralrimdva.mm"
include "cuni.mm"
include "wb.mm"
include "toponmax.mm"
include "fmfil.mm"
include "toponuni.mm"
include "fveq2d.mm"
include "eleqtrd.mm"
include "eqid.mm"
include "flimfnfcls.mm"
include "flfval.mm"
include "raleqdv.mm"
include "3bitr4d.mm"
include "sylibrd.mm"
include "imdistanda.mm"
include "cnpflf.mm"
include "impbid.mm"

theorem cnpfcf
  let cA: class A
  let vf: setvar f
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vg: setvar g
  let vh: setvar h
  let vx: setvar x
  let cL: class L

  disjoint A f
  disjoint F f
  disjoint J f
  disjoint K f
  disjoint X f
  disjoint Y f
  disjoint f g
  disjoint f h
  disjoint g h
  disjoint A g
  disjoint A h
  disjoint f x
  disjoint g x
  disjoint F g
  disjoint h x
  disjoint F h
  disjoint F x
  disjoint J g
  disjoint J h
  disjoint J x
  disjoint K g
  disjoint K h
  disjoint K x
  disjoint L f
  disjoint X g
  disjoint X h
  disjoint X x
  disjoint Y g
  disjoint Y h
  disjoint Y x
  assert |- ( ( J e. ( TopOn ` X ) /\ K e. ( TopOn ` Y ) /\ A e. X ) -> ( F e. ( ( J CnP K ) ` A ) <-> ( F : X --> Y /\ A. f e. ( Fil ` X ) ( A e. ( J fClus f ) -> ( F ` A ) e. ( ( K fClusf f ) ` F ) ) ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    cA
    cX
    wcel
    #
    w3a
    #
    cF
    cA
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    cX
    cY
    cF
    wf
    #
    cA
    cJ
    vf
    cv
    #
    cfcls
    co
    #
    wcel
    #
    cA
    cF
    cfv
    #
    cF
    cK
    @6
    cfcf
    co
    cfv
    #
    wcel
    #
    wi
    #
    vf
    cX
    cfil
    cfv
    #
    wral
    #
    wa
    #
    @3
    @4
    @15
    @3
    @4
    wa
    @5
    @14
    @0
    @1
    @4
    @5
    @2
    @0
    @1
    @4
    @5
    cA
    cF
    cJ
    cK
    cX
    cY
    cnpf2
    3expa
    3adantl3
    @1
    @0
    @4
    @14
    @2
    @1
    @4
    wa
    @12
    vf
    @13
    @1
    cK
    ctop
    wcel
    #
    @4
    @12
    cY
    cK
    topontop
    @16
    @4
    @8
    @11
    @16
    @8
    @4
    @11
    cA
    cF
    cJ
    cK
    @6
    cnpfcfi
    3com23
    3expia
    sylan
    ralrimivw
    3ad2antl2
    jca
    ex
    @3
    @15
    @5
    cA
    cJ
    vg
    cv
    #
    cflim
    co
    #
    wcel
    #
    @9
    cF
    cK
    @17
    cflf
    co
    cfv
    #
    wcel
    #
    wi
    #
    vg
    @13
    wral
    #
    wa
    @4
    @3
    @5
    @14
    @23
    @3
    @5
    wa
    #
    @14
    @22
    vg
    @13
    @24
    @17
    @13
    wcel
    #
    wa
    @19
    @14
    @21
    @24
    @25
    @19
    @14
    @21
    wi
    @24
    @25
    @19
    wa
    #
    wa
    #
    @14
    @17
    cY
    cF
    cfm
    co
    #
    cfv
    #
    vh
    cv
    #
    wss
    #
    @9
    cK
    @30
    cfcls
    co
    #
    wcel
    #
    wi
    #
    vh
    cY
    cfil
    cfv
    #
    wral
    #
    @21
    @27
    @14
    @34
    vh
    @35
    @27
    @30
    @35
    wcel
    #
    wa
    @31
    @14
    @33
    @27
    @37
    @31
    @14
    @33
    wi
    @27
    @37
    @31
    wa
    #
    wa
    #
    @14
    @17
    @6
    wss
    #
    @30
    @6
    @28
    cfv
    #
    wceq
    #
    wa
    #
    vf
    @13
    wrex
    #
    @33
    @39
    @17
    vf
    cF
    @30
    cY
    cX
    @39
    @25
    @17
    cX
    cfbas
    cfv
    wcel
    #
    @24
    @25
    @19
    @38
    simplrl
    @17
    cX
    filfbas
    #
    syl
    @27
    @37
    @31
    simprl
    @3
    @5
    @26
    @38
    simpllr
    @27
    @37
    @31
    simprr
    fmfnfm
    @14
    @44
    wa
    @12
    @43
    wa
    #
    vf
    @13
    wrex
    @39
    @33
    @12
    @43
    vf
    @13
    r19.29
    @39
    @47
    @33
    vf
    @13
    @39
    @6
    @13
    wcel
    #
    wa
    #
    @12
    @43
    @33
    @49
    @43
    @12
    @33
    @39
    @48
    @43
    @12
    @33
    wi
    @39
    @48
    @43
    wa
    #
    wa
    #
    @8
    @11
    @33
    @51
    cJ
    @6
    cflim
    co
    #
    @7
    cA
    @6
    cJ
    flimfcls
    @51
    @18
    @52
    cA
    @51
    @0
    @48
    @40
    @18
    @52
    wss
    @27
    @0
    @38
    @50
    @0
    @1
    @2
    @5
    @26
    simpll1
    ad2antrr
    @39
    @48
    @43
    simprl
    #
    @39
    @48
    @40
    @42
    simprrl
    @6
    @17
    cJ
    cX
    flimss2
    syl3anc
    @27
    @19
    @38
    @50
    @24
    @25
    @19
    simprr
    ad2antrr
    sseldd
    sseldi
    @51
    @11
    @33
    @51
    @10
    @32
    @9
    @51
    @10
    cK
    @41
    cfcls
    co
    #
    @32
    @51
    @1
    @48
    @5
    @10
    @54
    wceq
    @27
    @1
    @38
    @50
    @0
    @1
    @2
    @5
    @26
    simpll2
    #
    ad2antrr
    @53
    @27
    @5
    @38
    @50
    @3
    @5
    @26
    simplr
    #
    ad2antrr
    cF
    cK
    @6
    cY
    cX
    fcfval
    syl3anc
    @51
    @30
    @41
    cK
    cfcls
    @39
    @48
    @40
    @42
    simprrr
    oveq2d
    eqtr4d
    eleq2d
    biimpd
    embantd
    expr
    com23
    impd
    rexlimdva
    syl5
    mpan2d
    expr
    com23
    ralrimdva
    @27
    @9
    cK
    @29
    cflim
    co
    #
    wcel
    #
    @34
    vh
    cK
    cuni
    #
    cfil
    cfv
    #
    wral
    #
    @21
    @36
    @27
    @29
    @60
    wcel
    @58
    @61
    wb
    @27
    @29
    @35
    @60
    @27
    cY
    cK
    wcel
    #
    @45
    @5
    @29
    @35
    wcel
    @27
    @1
    @62
    @55
    cY
    cK
    toponmax
    syl
    @27
    @25
    @45
    @24
    @25
    @19
    simprl
    #
    @46
    syl
    @56
    cK
    @17
    cF
    cY
    cX
    fmfil
    syl3anc
    @27
    cY
    @59
    cfil
    @27
    @1
    cY
    @59
    wceq
    @55
    cY
    cK
    toponuni
    syl
    fveq2d
    #
    eleqtrd
    @9
    vh
    @29
    cK
    @59
    @59
    eqid
    flimfnfcls
    syl
    @27
    @20
    @57
    @9
    @27
    @1
    @25
    @5
    @20
    @57
    wceq
    @55
    @63
    @56
    cF
    cK
    @17
    cY
    cX
    flfval
    syl3anc
    eleq2d
    @27
    @34
    vh
    @35
    @60
    @64
    raleqdv
    3bitr4d
    sylibrd
    expr
    com23
    ralrimdva
    imdistanda
    cA
    vg
    cF
    cJ
    cK
    cX
    cY
    cnpflf
    sylibrd
    impbid
end
