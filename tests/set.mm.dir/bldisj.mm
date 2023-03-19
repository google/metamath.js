include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "cxr.mm"
include "cxad.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cbl.mm"
include "cin.mm"
include "cv.mm"
include "clt.mm"
include "wn.mm"
include "simpr3.mm"
include "wb.mm"
include "simpr1.mm"
include "simpr2.mm"
include "xaddcld.mm"
include "xmetcl.mm"
include "adantr.mm"
include "xrlenlt.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "elin.mm"
include "simpl1.mm"
include "simpl2.mm"
include "elbl.mm"
include "syl3anc.mm"
include "simpl3.mm"
include "anbi12d.mm"
include "anandi.mm"
include "syl6bbr.mm"
include "wi.mm"
include "simpr.mm"
include "xlt2add.mm"
include "syl22anc.mm"
include "xmettri3.mm"
include "syl13anc.mm"
include "xrlelttr.mm"
include "mpand.mm"
include "syld.mm"
include "expimpd.mm"
include "sylbid.mm"
include "syl5bi.mm"
include "mtod.mm"
include "eq0rdv.mm"

theorem bldisj
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cX: class X
  let cA: class A
  let vx: setvar x
  let vr: setvar r
  let vy: setvar y
  let wph: wff ph


  assert |- ( ( ( D e. ( *Met ` X ) /\ P e. X /\ Q e. X ) /\ ( R e. RR* /\ S e. RR* /\ ( R +e S ) <_ ( P D Q ) ) ) -> ( ( P ( ball ` D ) R ) i^i ( Q ( ball ` D ) S ) ) = (/) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cP
    cX
    wcel
    #
    cQ
    cX
    wcel
    #
    w3a
    #
    cR
    cxr
    wcel
    #
    cS
    cxr
    wcel
    #
    cR
    cS
    cxad
    co
    #
    cP
    cQ
    cD
    co
    #
    cle
    wbr
    #
    w3a
    #
    wa
    #
    vx
    cP
    cR
    cD
    cbl
    cfv
    #
    co
    #
    cQ
    cS
    @11
    co
    #
    cin
    #
    @10
    vx
    cv
    #
    @14
    wcel
    #
    @7
    @6
    clt
    wbr
    #
    @10
    @8
    @17
    wn
    #
    @3
    @4
    @5
    @8
    simpr3
    @10
    @6
    cxr
    wcel
    #
    @7
    cxr
    wcel
    #
    @8
    @18
    wb
    @10
    cR
    cS
    @3
    @4
    @5
    @8
    simpr1
    #
    @3
    @4
    @5
    @8
    simpr2
    #
    xaddcld
    #
    @3
    @20
    @9
    cP
    cQ
    cD
    cX
    xmetcl
    adantr
    #
    @6
    @7
    xrlenlt
    syl2anc
    mpbid
    @16
    @15
    @12
    wcel
    #
    @15
    @13
    wcel
    #
    wa
    #
    @10
    @17
    @15
    @12
    @13
    elin
    @10
    @27
    @15
    cX
    wcel
    #
    cP
    @15
    cD
    co
    #
    cR
    clt
    wbr
    #
    cQ
    @15
    cD
    co
    #
    cS
    clt
    wbr
    #
    wa
    #
    wa
    #
    @17
    @10
    @27
    @28
    @30
    wa
    #
    @28
    @32
    wa
    #
    wa
    @34
    @10
    @25
    @35
    @26
    @36
    @10
    @0
    @1
    @4
    @25
    @35
    wb
    @0
    @1
    @2
    @9
    simpl1
    #
    @0
    @1
    @2
    @9
    simpl2
    #
    @21
    @15
    cD
    cP
    cR
    cX
    elbl
    syl3anc
    @10
    @0
    @2
    @5
    @26
    @36
    wb
    @37
    @0
    @1
    @2
    @9
    simpl3
    #
    @22
    @15
    cD
    cQ
    cS
    cX
    elbl
    syl3anc
    anbi12d
    @28
    @30
    @32
    anandi
    syl6bbr
    @10
    @28
    @33
    @17
    @10
    @28
    wa
    #
    @33
    @29
    @31
    cxad
    co
    #
    @6
    clt
    wbr
    #
    @17
    @40
    @29
    cxr
    wcel
    #
    @31
    cxr
    wcel
    #
    @4
    @5
    @33
    @42
    wi
    @40
    @0
    @1
    @28
    @43
    @10
    @0
    @28
    @37
    adantr
    #
    @10
    @1
    @28
    @38
    adantr
    #
    @10
    @28
    simpr
    #
    cP
    @15
    cD
    cX
    xmetcl
    syl3anc
    #
    @40
    @0
    @2
    @28
    @44
    @45
    @10
    @2
    @28
    @39
    adantr
    #
    @47
    cQ
    @15
    cD
    cX
    xmetcl
    syl3anc
    #
    @10
    @4
    @28
    @21
    adantr
    @10
    @5
    @28
    @22
    adantr
    @29
    @31
    cR
    cS
    xlt2add
    syl22anc
    @40
    @7
    @41
    cle
    wbr
    #
    @42
    @17
    @40
    @0
    @1
    @2
    @28
    @51
    @45
    @46
    @49
    @47
    cP
    cQ
    @15
    cD
    cX
    xmettri3
    syl13anc
    @40
    @20
    @41
    cxr
    wcel
    @19
    @51
    @42
    wa
    @17
    wi
    @10
    @20
    @28
    @24
    adantr
    @40
    @29
    @31
    @48
    @50
    xaddcld
    @10
    @19
    @28
    @23
    adantr
    @7
    @41
    @6
    xrlelttr
    syl3anc
    mpand
    syld
    expimpd
    sylbid
    syl5bi
    mtod
    eq0rdv
end
