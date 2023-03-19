include "cv.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "wcel.mm"
include "wreu.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "cword.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "cpfx.mm"
include "s1eq.mm"
include "oveq2d.mm"
include "eleq1d.mm"
include "reu8.mm"
include "wb.mm"
include "simprl.mm"
include "simpl.mm"
include "ad2antrr.mm"
include "anim1i.mm"
include "simplrr.mm"
include "simp-4r.mm"
include "reuccatpfxs1lem.mm"
include "syl3anc.mm"
include "clsw.mm"
include "adantr.mm"
include "lswccats1.mm"
include "syl.mm"
include "eqcomd.mm"
include "s1eqd.mm"
include "id.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "adantl.mm"
include "mpbird.mm"
include "w3a.mm"
include "eleq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "rspcva.mm"
include "3anass.mm"
include "simplbi2com.mm"
include "ex.mm"
include "com13.mm"
include "imp.mm"
include "ccats1pfxeqbi.mm"
include "impbid.mm"
include "ralrimiva.mm"
include "reu6i.mm"
include "syl2anc.mm"
include "rexlimdva.mm"
include "syl5bi.mm"

theorem reuccatpfxs1
  let vx: setvar x
  let vw: setvar w
  let vv: setvar v
  let cV: class V
  let cW: class W
  let cX: class X
  let vu: setvar u
  let vk: setvar k

  disjoint V v
  disjoint V w
  disjoint V x
  disjoint v w
  disjoint v x
  disjoint w x
  disjoint W v
  disjoint W w
  disjoint W x
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint V u
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint W u
  disjoint X u
  disjoint k x
  assert |- ( ( W e. Word V /\ A. x e. X ( x e. Word V /\ ( # ` x ) = ( ( # ` W ) + 1 ) ) ) -> ( E! v e. V ( W ++ <" v "> ) e. X -> E! w e. X W = ( w prefix ( # ` W ) ) ) )

  proof
    cW
    vv
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
    vv
    cV
    wreu
    @3
    cW
    vu
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
    vv
    vu
    weq
    #
    wi
    vu
    cV
    wral
    #
    wa
    #
    vv
    cV
    wrex
    cW
    cV
    cword
    #
    wcel
    #
    vx
    cv
    #
    @11
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
    vw
    cv
    #
    @16
    cpfx
    co
    wceq
    #
    vw
    cX
    wreu
    #
    @3
    @7
    vv
    vu
    cV
    @8
    @2
    @6
    cX
    @8
    @1
    @5
    cW
    cconcat
    @0
    @4
    s1eq
    oveq2d
    eleq1d
    reu8
    @21
    @10
    @24
    vv
    cV
    @21
    @0
    cV
    wcel
    #
    wa
    #
    @10
    @24
    @26
    @10
    wa
    #
    @3
    @23
    @22
    @2
    wceq
    #
    wb
    #
    vw
    cX
    wral
    @24
    @26
    @3
    @9
    simprl
    @27
    @29
    vw
    cX
    @27
    @22
    cX
    wcel
    #
    wa
    #
    @23
    @28
    @31
    @12
    @30
    wa
    @9
    @20
    @23
    @28
    wi
    @27
    @12
    @30
    @21
    @12
    @25
    @10
    @12
    @20
    simpl
    #
    ad2antrr
    anim1i
    @26
    @3
    @9
    @30
    simplrr
    @12
    @20
    @25
    @10
    @30
    simp-4r
    vx
    @0
    @22
    cV
    cW
    cX
    vu
    reuccatpfxs1lem
    syl3anc
    @31
    @28
    @23
    @31
    @28
    wa
    #
    @23
    @22
    cW
    @22
    clsw
    cfv
    #
    cs1
    #
    cconcat
    co
    #
    wceq
    #
    @33
    @37
    @2
    cW
    @2
    clsw
    cfv
    #
    cs1
    #
    cconcat
    co
    #
    wceq
    #
    @33
    @1
    @39
    cW
    cconcat
    @33
    @0
    @38
    @33
    @38
    @0
    @33
    @12
    @25
    wa
    #
    @38
    @0
    wceq
    @27
    @42
    @30
    @28
    @26
    @42
    @10
    @21
    @12
    @25
    @32
    anim1i
    adantr
    ad2antrr
    @0
    cV
    cW
    lswccats1
    syl
    eqcomd
    s1eqd
    oveq2d
    @28
    @37
    @41
    wb
    @31
    @28
    @22
    @2
    @36
    @40
    @28
    id
    @28
    @35
    @39
    cW
    cconcat
    @28
    @34
    @38
    @22
    @2
    clsw
    fveq2
    s1eqd
    oveq2d
    eqeq12d
    adantl
    mpbird
    @33
    @12
    @22
    @11
    wcel
    #
    @22
    chash
    cfv
    #
    @17
    wceq
    #
    w3a
    #
    @23
    @37
    wb
    @31
    @46
    @28
    @27
    @30
    @46
    @21
    @30
    @46
    wi
    #
    @25
    @10
    @12
    @20
    @47
    @30
    @20
    @12
    @46
    @30
    @20
    @12
    @46
    wi
    #
    @30
    @20
    wa
    @43
    @45
    wa
    #
    @48
    @19
    @49
    vx
    @22
    cX
    vx
    vw
    weq
    #
    @14
    @43
    @18
    @45
    @13
    @22
    @11
    eleq1
    @50
    @15
    @44
    @17
    @13
    @22
    chash
    fveq2
    eqeq1d
    anbi12d
    rspcva
    @46
    @12
    @49
    @12
    @43
    @45
    3anass
    simplbi2com
    syl
    ex
    com13
    imp
    ad2antrr
    imp
    adantr
    @22
    cV
    cW
    ccats1pfxeqbi
    syl
    mpbird
    ex
    impbid
    ralrimiva
    @23
    vw
    cX
    @2
    reu6i
    syl2anc
    ex
    rexlimdva
    syl5bi
end
