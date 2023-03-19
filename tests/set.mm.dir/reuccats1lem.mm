include "cword.mm"
include "wcel.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "w3a.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "wa.mm"
include "cc0.mm"
include "cop.mm"
include "csubstr.mm"
include "eleq1.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "rspcv.mm"
include "adantl.mm"
include "wrex.mm"
include "simpl.mm"
include "adantr.mm"
include "simprr.mm"
include "ccats1swrdeqrex.mm"
include "syl3anc.mm"
include "weq.mm"
include "s1eq.mm"
include "oveq2d.mm"
include "eleq1d.mm"
include "eqeq2.mm"
include "imbi12d.mm"
include "biimpac.mm"
include "eqcoms.mm"
include "eqeq2d.mm"
include "biimpd.mm"
include "imim2i.mm"
include "com13.mm"
include "mpd.mm"
include "ex.mm"
include "com23.mm"
include "sylan9r.mm"
include "rexlimdva.mm"
include "syld.mm"
include "impd.mm"
include "3adant3.mm"
include "imp.mm"

theorem reuccats1lem
  let vx: setvar x
  let cS: class S
  let cU: class U
  let cV: class V
  let cW: class W
  let cX: class X
  let vs: setvar s
  let vu: setvar u

  disjoint S s
  disjoint U x
  disjoint V s
  disjoint V x
  disjoint s x
  disjoint W s
  disjoint W x
  disjoint X s
  disjoint X x
  disjoint S u
  disjoint s u
  disjoint U u
  disjoint u x
  disjoint V u
  disjoint W u
  disjoint X u
  assert |- ( ( ( W e. Word V /\ U e. X /\ ( W ++ <" S "> ) e. X ) /\ ( A. s e. V ( ( W ++ <" s "> ) e. X -> S = s ) /\ A. x e. X ( x e. Word V /\ ( # ` x ) = ( ( # ` W ) + 1 ) ) ) ) -> ( W = ( U substr <. 0 , ( # ` W ) >. ) -> U = ( W ++ <" S "> ) ) )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cU
    cX
    wcel
    #
    cW
    cS
    cs1
    #
    cconcat
    co
    #
    cX
    wcel
    #
    w3a
    cW
    vs
    cv
    #
    cs1
    #
    cconcat
    co
    #
    cX
    wcel
    #
    cS
    @6
    wceq
    #
    wi
    #
    vs
    cV
    wral
    #
    vx
    cv
    #
    @0
    wcel
    #
    @13
    chash
    cfv
    #
    cW
    chash
    cfv
    #
    c1
    caddc
    co
    #
    wceq
    #
    wa
    #
    vx
    cX
    wral
    #
    wa
    #
    cW
    cU
    cc0
    @16
    cop
    csubstr
    co
    wceq
    #
    cU
    @4
    wceq
    #
    wi
    #
    @1
    @2
    @21
    @24
    wi
    @5
    @1
    @2
    wa
    #
    @12
    @20
    @24
    @25
    @20
    @12
    @24
    @25
    @20
    cU
    @0
    wcel
    #
    cU
    chash
    cfv
    #
    @17
    wceq
    #
    wa
    #
    @12
    @24
    wi
    #
    @2
    @20
    @29
    wi
    @1
    @19
    @29
    vx
    cU
    cX
    @13
    cU
    wceq
    #
    @14
    @26
    @18
    @28
    @13
    cU
    @0
    eleq1
    @31
    @15
    @27
    @17
    @13
    cU
    chash
    fveq2
    eqeq1d
    anbi12d
    rspcv
    adantl
    @25
    @29
    @30
    @25
    @29
    wa
    #
    @22
    @12
    @23
    @32
    @22
    cU
    cW
    vu
    cv
    #
    cs1
    #
    cconcat
    co
    #
    wceq
    #
    vu
    cV
    wrex
    #
    @12
    @23
    wi
    #
    @32
    @1
    @26
    @28
    @22
    @37
    wi
    @25
    @1
    @29
    @1
    @2
    simpl
    adantr
    @29
    @26
    @25
    @26
    @28
    simpl
    adantl
    @25
    @26
    @28
    simprr
    cU
    cV
    cW
    vu
    ccats1swrdeqrex
    syl3anc
    @25
    @37
    @38
    wi
    #
    @29
    @2
    @39
    @1
    @2
    @36
    @38
    vu
    cV
    @2
    @33
    cV
    wcel
    #
    wa
    @12
    @36
    @23
    @40
    @12
    @35
    cX
    wcel
    #
    cS
    @33
    wceq
    #
    wi
    #
    @2
    @36
    @23
    wi
    #
    @11
    @43
    vs
    @33
    cV
    vs
    vu
    weq
    #
    @9
    @41
    @10
    @42
    @45
    @8
    @35
    cX
    @45
    @7
    @34
    cW
    cconcat
    @6
    @33
    s1eq
    oveq2d
    eleq1d
    @6
    @33
    cS
    eqeq2
    imbi12d
    rspcv
    @2
    @36
    @43
    @23
    @2
    @36
    @43
    @23
    wi
    #
    @2
    @36
    wa
    @41
    @46
    @36
    @2
    @41
    cU
    @35
    cX
    eleq1
    biimpac
    @36
    @41
    @46
    wi
    @2
    @43
    @41
    @36
    @23
    @42
    @44
    @41
    @42
    @36
    @23
    @42
    @35
    @4
    cU
    @42
    @34
    @3
    cW
    cconcat
    @34
    @3
    wceq
    @33
    cS
    @33
    cS
    s1eq
    eqcoms
    oveq2d
    eqeq2d
    biimpd
    imim2i
    com13
    adantl
    mpd
    ex
    com23
    sylan9r
    com23
    rexlimdva
    adantl
    adantr
    syld
    com23
    ex
    syld
    com23
    impd
    3adant3
    imp
end
