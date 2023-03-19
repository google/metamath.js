include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "cple.mm"
include "cfv.mm"
include "wn.mm"
include "catm.mm"
include "wrex.mm"
include "cplt.mm"
include "wi.mm"
include "clat.mm"
include "hllat.mm"
include "latmcl.mm"
include "syl3an1.mm"
include "eqid.mm"
include "cvrlt.mm"
include "ex.mm"
include "syld3an2.mm"
include "hlrelat1.mm"
include "syld.mm"
include "imp.mm"
include "wb.mm"
include "simpl1.mm"
include "syl.mm"
include "atbase.mm"
include "adantl.mm"
include "simpl2.mm"
include "simpl3.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "biimpd.mm"
include "expcomd.mm"
include "con3.mm"
include "syl6.mm"
include "com23.mm"
include "a1d.mm"
include "imp4d.mm"
include "simpr.mm"
include "cvr1.mm"
include "syl3anc.mm"
include "sylibd.mm"
include "wceq.mm"
include "latjass.mm"
include "latabs1.mm"
include "adantr.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "latnle.mm"
include "latmle2.mm"
include "biantrurd.mm"
include "latjle12.mm"
include "bitrd.mm"
include "anbi12d.mm"
include "cpo.mm"
include "hlpos.mm"
include "latjcl.mm"
include "3jca.mm"
include "cvrnbtwn2.mm"
include "3exp.mm"
include "sylc.mm"
include "sylbid.mm"
include "imp32.mm"
include "oveq2d.mm"
include "sylanl2.mm"
include "breqtrd.mm"
include "expr.mm"
include "an32s.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem cvrexchlem
  let cB: class B
  let cC: class C
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  let vp: setvar p
  assume cvrexch.b: |- B = ( Base ` K )
  assume cvrexch.j: |- .\/ = ( join ` K )
  assume cvrexch.m: |- ./\ = ( meet ` K )
  assume cvrexch.c: |- C = ( <o ` K )


  assert |- ( ( K e. HL /\ X e. B /\ Y e. B ) -> ( ( X ./\ Y ) C Y -> X C ( X .\/ Y ) ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cX
    cY
    c.an
    co
    #
    cY
    cC
    wbr
    #
    cX
    cX
    cY
    c.or
    co
    #
    cC
    wbr
    #
    @3
    @5
    wa
    #
    vp
    cv
    #
    @4
    cK
    cple
    cfv
    #
    wbr
    #
    wn
    #
    @9
    cY
    @10
    wbr
    #
    wa
    #
    vp
    cK
    catm
    cfv
    #
    wrex
    #
    @7
    @3
    @5
    @16
    @3
    @5
    @4
    cY
    cK
    cplt
    cfv
    #
    wbr
    #
    @16
    @0
    @4
    cB
    wcel
    #
    @1
    @2
    @5
    @18
    wi
    @0
    cK
    clat
    wcel
    #
    @1
    @2
    @19
    cK
    hllat
    #
    cB
    cK
    c.an
    cX
    cY
    cvrexch.b
    cvrexch.m
    latmcl
    #
    syl3an1
    #
    @0
    @19
    @2
    w3a
    @5
    @18
    chlt
    cB
    cC
    @17
    cK
    @4
    cY
    cvrexch.b
    @17
    eqid
    #
    cvrexch.c
    cvrlt
    ex
    syld3an2
    @0
    @19
    @1
    @2
    @18
    @16
    wi
    @23
    @15
    cB
    @17
    cK
    @10
    @4
    cY
    vp
    cvrexch.b
    @10
    eqid
    #
    @24
    @15
    eqid
    #
    hlrelat1
    syld3an2
    syld
    imp
    @8
    @14
    @7
    vp
    @15
    @3
    @9
    @15
    wcel
    #
    @5
    @14
    @7
    wi
    @3
    @27
    wa
    #
    @5
    @14
    @7
    @28
    @5
    @14
    wa
    #
    wa
    cX
    cX
    @9
    c.or
    co
    #
    @6
    cC
    @28
    @29
    cX
    @30
    cC
    wbr
    #
    @28
    @29
    @9
    cX
    @10
    wbr
    #
    wn
    #
    @31
    @28
    @5
    @12
    @13
    @33
    @28
    @12
    @13
    @33
    wi
    wi
    @5
    @28
    @13
    @12
    @33
    @28
    @13
    @32
    @11
    wi
    @12
    @33
    wi
    @28
    @32
    @13
    @11
    @28
    @32
    @13
    wa
    #
    @11
    @28
    @20
    @9
    cB
    wcel
    #
    @1
    @2
    @34
    @11
    wb
    @28
    @0
    @20
    @0
    @1
    @2
    @27
    simpl1
    #
    @21
    syl
    @27
    @35
    @3
    @15
    cB
    @9
    cK
    cvrexch.b
    @26
    atbase
    #
    adantl
    @0
    @1
    @2
    @27
    simpl2
    #
    @0
    @1
    @2
    @27
    simpl3
    cB
    cK
    @10
    c.an
    @9
    cX
    cY
    cvrexch.b
    @25
    cvrexch.m
    latlem12
    syl13anc
    biimpd
    expcomd
    @32
    @11
    con3
    syl6
    com23
    a1d
    imp4d
    @28
    @0
    @1
    @27
    @33
    @31
    wb
    @36
    @38
    @3
    @27
    simpr
    @15
    cB
    cC
    @9
    c.or
    cK
    @10
    cX
    cvrexch.b
    @25
    cvrexch.j
    cvrexch.c
    @26
    cvr1
    syl3anc
    sylibd
    imp
    @27
    @3
    @35
    @29
    @30
    @6
    wceq
    @37
    @3
    @35
    wa
    #
    @29
    wa
    #
    cX
    @4
    @9
    c.or
    co
    #
    c.or
    co
    #
    @30
    @6
    @39
    @42
    @30
    wceq
    @29
    @39
    cX
    @4
    c.or
    co
    #
    @9
    c.or
    co
    #
    @42
    @30
    @39
    @20
    @1
    @19
    @35
    @44
    @42
    wceq
    @39
    @0
    @20
    @0
    @1
    @2
    @35
    simpl1
    #
    @21
    syl
    #
    @0
    @1
    @2
    @35
    simpl2
    #
    @39
    @20
    @1
    @2
    @19
    @46
    @47
    @0
    @1
    @2
    @35
    simpl3
    #
    @22
    syl3anc
    #
    @3
    @35
    simpr
    #
    cB
    c.or
    cK
    cX
    @4
    @9
    cvrexch.b
    cvrexch.j
    latjass
    syl13anc
    @39
    @43
    cX
    @9
    c.or
    @3
    @43
    cX
    wceq
    #
    @35
    @0
    @20
    @1
    @2
    @51
    @21
    cB
    c.or
    cK
    c.an
    cX
    cY
    cvrexch.b
    cvrexch.j
    cvrexch.m
    latabs1
    syl3an1
    adantr
    oveq1d
    eqtr3d
    adantr
    @40
    @41
    cY
    cX
    c.or
    @39
    @5
    @14
    @41
    cY
    wceq
    #
    @39
    @14
    @5
    @52
    @39
    @14
    @4
    @41
    @17
    wbr
    #
    @41
    cY
    @10
    wbr
    #
    wa
    #
    @5
    @52
    wi
    @39
    @12
    @53
    @13
    @54
    @39
    @20
    @19
    @35
    @12
    @53
    wb
    @46
    @49
    @50
    cB
    @17
    c.or
    cK
    @10
    @4
    @9
    cvrexch.b
    @25
    @24
    cvrexch.j
    latnle
    syl3anc
    @39
    @13
    @4
    cY
    @10
    wbr
    #
    @13
    wa
    #
    @54
    @39
    @56
    @13
    @39
    @20
    @1
    @2
    @56
    @46
    @47
    @48
    cB
    cK
    @10
    c.an
    cX
    cY
    cvrexch.b
    @25
    cvrexch.m
    latmle2
    syl3anc
    biantrurd
    @39
    @20
    @19
    @35
    @2
    @57
    @54
    wb
    @46
    @49
    @50
    @48
    cB
    c.or
    cK
    @10
    @4
    @9
    cY
    cvrexch.b
    @25
    cvrexch.j
    latjle12
    syl13anc
    bitrd
    anbi12d
    @39
    @5
    @55
    @52
    @39
    cK
    cpo
    wcel
    #
    @19
    @2
    @41
    cB
    wcel
    #
    w3a
    #
    @5
    @55
    @52
    wi
    #
    wi
    @39
    @0
    @58
    @45
    cK
    hlpos
    syl
    @39
    @19
    @2
    @59
    @49
    @48
    @39
    @20
    @19
    @35
    @59
    @46
    @49
    @50
    cB
    c.or
    cK
    @4
    @9
    cvrexch.b
    cvrexch.j
    latjcl
    syl3anc
    3jca
    @58
    @60
    @5
    @61
    @58
    @60
    @5
    w3a
    @55
    @52
    cB
    cC
    @17
    cK
    @10
    @4
    cY
    @41
    cvrexch.b
    @25
    @24
    cvrexch.c
    cvrnbtwn2
    biimpd
    3exp
    sylc
    com23
    sylbid
    com23
    imp32
    oveq2d
    eqtr3d
    sylanl2
    breqtrd
    expr
    an32s
    rexlimdva
    mpd
    ex
end
