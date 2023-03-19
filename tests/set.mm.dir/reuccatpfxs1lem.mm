include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "cpfx.mm"
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
include "ccats1pfxeqrex.mm"
include "syl3anc.mm"
include "weq.mm"
include "s1eq.mm"
include "oveq2d.mm"
include "eleq1d.mm"
include "eqeq2.mm"
include "imbi12d.mm"
include "id.mm"
include "imp.mm"
include "eqcomd.mm"
include "s1eqd.mm"
include "eqeq2d.mm"
include "biimpd.mm"
include "ex.mm"
include "com13.mm"
include "sylbid.mm"
include "com3l.mm"
include "sylan9r.mm"
include "com23.mm"
include "rexlimdva.mm"
include "syld.mm"
include "3imp.mm"

theorem reuccatpfxs1lem
  let vx: setvar x
  let cS: class S
  let cU: class U
  let cV: class V
  let cW: class W
  let cX: class X
  let vs: setvar s
  let vu: setvar u
  let vk: setvar k

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
  disjoint k x
  assert |- ( ( ( W e. Word V /\ U e. X ) /\ A. s e. V ( ( W ++ <" s "> ) e. X -> S = s ) /\ A. x e. X ( x e. Word V /\ ( # ` x ) = ( ( # ` W ) + 1 ) ) ) -> ( W = ( U prefix ( # ` W ) ) -> U = ( W ++ <" S "> ) ) )

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
    wa
    #
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
    @4
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
    @11
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
    cW
    cU
    @14
    cpfx
    co
    wceq
    #
    cU
    cW
    cS
    cs1
    #
    cconcat
    co
    #
    wceq
    #
    wi
    #
    @3
    @18
    @10
    @23
    @3
    @18
    cU
    @0
    wcel
    #
    cU
    chash
    cfv
    #
    @15
    wceq
    #
    wa
    #
    @10
    @23
    wi
    #
    @2
    @18
    @27
    wi
    @1
    @17
    @27
    vx
    cU
    cX
    @11
    cU
    wceq
    #
    @12
    @24
    @16
    @26
    @11
    cU
    @0
    eleq1
    @29
    @13
    @25
    @15
    @11
    cU
    chash
    fveq2
    eqeq1d
    anbi12d
    rspcv
    adantl
    @3
    @27
    @28
    @3
    @27
    wa
    #
    @19
    @10
    @22
    @30
    @19
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
    @10
    @22
    wi
    #
    @30
    @1
    @24
    @26
    @19
    @35
    wi
    @3
    @1
    @27
    @1
    @2
    simpl
    adantr
    @27
    @24
    @3
    @24
    @26
    simpl
    adantl
    @3
    @24
    @26
    simprr
    cU
    cV
    cW
    vu
    ccats1pfxeqrex
    syl3anc
    @3
    @35
    @36
    wi
    #
    @27
    @2
    @37
    @1
    @2
    @34
    @36
    vu
    cV
    @2
    @31
    cV
    wcel
    #
    wa
    @10
    @34
    @22
    @38
    @10
    @33
    cX
    wcel
    #
    cS
    @31
    wceq
    #
    wi
    #
    @2
    @34
    @22
    wi
    #
    @9
    @41
    vs
    @31
    cV
    vs
    vu
    weq
    #
    @7
    @39
    @8
    @40
    @43
    @6
    @33
    cX
    @43
    @5
    @32
    cW
    cconcat
    @4
    @31
    s1eq
    oveq2d
    eleq1d
    @4
    @31
    cS
    eqeq2
    imbi12d
    rspcv
    @34
    @2
    @41
    @22
    @34
    @2
    @39
    @41
    @22
    wi
    cU
    @33
    cX
    eleq1
    @41
    @39
    @34
    @22
    @41
    @39
    @42
    @41
    @39
    wa
    #
    @34
    @22
    @44
    @33
    @21
    cU
    @44
    @32
    @20
    cW
    cconcat
    @44
    @31
    cS
    @44
    cS
    @31
    @41
    @39
    @40
    @41
    id
    imp
    eqcomd
    s1eqd
    oveq2d
    eqeq2d
    biimpd
    ex
    com13
    sylbid
    com3l
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
    3imp
end
