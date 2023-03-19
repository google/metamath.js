include "cn0.mm"
include "wcel.mm"
include "w3a.mm"
include "csrg.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wa.mm"
include "cv.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "c0g.mm"
include "cfv.mm"
include "simpr.mm"
include "adantr.mm"
include "eqid.mm"
include "srglz.mm"
include "syl2anc.mm"
include "simpl.mm"
include "mulg0.mm"
include "syl.mm"
include "srgcl.mm"
include "syl3anc.mm"
include "3eqtr4d.mm"
include "cplusg.mm"
include "cmnd.mm"
include "srgmnd.mm"
include "adantl.mm"
include "mulgnn0p1.mm"
include "mulgnn0cl.mm"
include "srgdir.mm"
include "syl13anc.mm"
include "eqtrd.mm"
include "3expb.mm"
include "ancoms.mm"
include "eqcomd.mm"
include "sylan9eqr.mm"
include "exp31.mm"
include "a2d.mm"
include "nn0ind.mm"
include "expd.mm"
include "3impib.mm"
include "impcom.mm"

theorem srgmulgass
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let cN: class N
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume srgmulgass.b: |- B = ( Base ` R )
  assume srgmulgass.m: |- .x. = ( .g ` R )
  assume srgmulgass.t: |- .X. = ( .r ` R )


  assert |- ( ( R e. SRing /\ ( N e. NN0 /\ X e. B /\ Y e. B ) ) -> ( ( N .x. X ) .X. Y ) = ( N .x. ( X .X. Y ) ) )

  proof
    cN
    cn0
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
    cR
    csrg
    wcel
    #
    cN
    cX
    c.x
    co
    #
    cY
    c.xp
    co
    #
    cN
    cX
    cY
    c.xp
    co
    #
    c.x
    co
    #
    wceq
    #
    @0
    @1
    @2
    @3
    @8
    wi
    @0
    @1
    @2
    wa
    #
    @3
    @8
    @9
    @3
    wa
    #
    vx
    cv
    #
    cX
    c.x
    co
    #
    cY
    c.xp
    co
    #
    @11
    @6
    c.x
    co
    #
    wceq
    #
    wi
    @10
    cc0
    cX
    c.x
    co
    #
    cY
    c.xp
    co
    #
    cc0
    @6
    c.x
    co
    #
    wceq
    #
    wi
    @10
    vy
    cv
    #
    cX
    c.x
    co
    #
    cY
    c.xp
    co
    #
    @20
    @6
    c.x
    co
    #
    wceq
    #
    wi
    @10
    @20
    c1
    caddc
    co
    #
    cX
    c.x
    co
    #
    cY
    c.xp
    co
    #
    @25
    @6
    c.x
    co
    #
    wceq
    #
    wi
    @10
    @8
    wi
    vx
    vy
    cN
    @11
    cc0
    wceq
    #
    @15
    @19
    @10
    @30
    @13
    @17
    @14
    @18
    @30
    @12
    @16
    cY
    c.xp
    @11
    cc0
    cX
    c.x
    oveq1
    oveq1d
    @11
    cc0
    @6
    c.x
    oveq1
    eqeq12d
    imbi2d
    vx
    vy
    weq
    #
    @15
    @24
    @10
    @31
    @13
    @22
    @14
    @23
    @31
    @12
    @21
    cY
    c.xp
    @11
    @20
    cX
    c.x
    oveq1
    oveq1d
    @11
    @20
    @6
    c.x
    oveq1
    eqeq12d
    imbi2d
    @11
    @25
    wceq
    #
    @15
    @29
    @10
    @32
    @13
    @27
    @14
    @28
    @32
    @12
    @26
    cY
    c.xp
    @11
    @25
    cX
    c.x
    oveq1
    oveq1d
    @11
    @25
    @6
    c.x
    oveq1
    eqeq12d
    imbi2d
    @11
    cN
    wceq
    #
    @15
    @8
    @10
    @33
    @13
    @5
    @14
    @7
    @33
    @12
    @4
    cY
    c.xp
    @11
    cN
    cX
    c.x
    oveq1
    oveq1d
    @11
    cN
    @6
    c.x
    oveq1
    eqeq12d
    imbi2d
    @10
    cR
    c0g
    cfv
    #
    cY
    c.xp
    co
    #
    @34
    @17
    @18
    @10
    @3
    @2
    @35
    @34
    wceq
    @9
    @3
    simpr
    #
    @9
    @2
    @3
    @1
    @2
    simpr
    adantr
    #
    cB
    cR
    c.xp
    cY
    @34
    srgmulgass.b
    srgmulgass.t
    @34
    eqid
    #
    srglz
    syl2anc
    @10
    @16
    @34
    cY
    c.xp
    @10
    @1
    @16
    @34
    wceq
    @9
    @1
    @3
    @1
    @2
    simpl
    adantr
    #
    cB
    c.x
    cR
    cX
    @34
    srgmulgass.b
    @38
    srgmulgass.m
    mulg0
    syl
    oveq1d
    @10
    @6
    cB
    wcel
    #
    @18
    @34
    wceq
    @10
    @3
    @1
    @2
    @40
    @36
    @39
    @37
    cB
    cR
    c.xp
    cX
    cY
    srgmulgass.b
    srgmulgass.t
    srgcl
    #
    syl3anc
    cB
    c.x
    cR
    @6
    @34
    srgmulgass.b
    @38
    srgmulgass.m
    mulg0
    syl
    3eqtr4d
    @20
    cn0
    wcel
    #
    @10
    @24
    @29
    @42
    @10
    @24
    @29
    @42
    @10
    wa
    #
    @24
    wa
    @27
    @22
    @6
    cR
    cplusg
    cfv
    #
    co
    #
    @28
    @43
    @27
    @45
    wceq
    @24
    @43
    @27
    @21
    cX
    @44
    co
    #
    cY
    c.xp
    co
    #
    @45
    @43
    @26
    @46
    cY
    c.xp
    @43
    cR
    cmnd
    wcel
    #
    @42
    @1
    @26
    @46
    wceq
    @10
    @48
    @42
    @3
    @48
    @9
    cR
    srgmnd
    adantl
    adantl
    #
    @42
    @10
    simpl
    #
    @10
    @1
    @42
    @39
    adantl
    #
    cB
    @44
    c.x
    cR
    @20
    cX
    srgmulgass.b
    srgmulgass.m
    @44
    eqid
    #
    mulgnn0p1
    syl3anc
    oveq1d
    @43
    @3
    @21
    cB
    wcel
    #
    @1
    @2
    @47
    @45
    wceq
    @10
    @3
    @42
    @36
    adantl
    @43
    @48
    @42
    @1
    @53
    @49
    @50
    @51
    cB
    c.x
    cR
    @20
    cX
    srgmulgass.b
    srgmulgass.m
    mulgnn0cl
    syl3anc
    @51
    @10
    @2
    @42
    @37
    adantl
    cB
    @44
    cR
    c.xp
    @21
    cX
    cY
    srgmulgass.b
    @52
    srgmulgass.t
    srgdir
    syl13anc
    eqtrd
    adantr
    @24
    @43
    @45
    @23
    @6
    @44
    co
    #
    @28
    @22
    @23
    @6
    @44
    oveq1
    @43
    @28
    @54
    @43
    @48
    @42
    @40
    @28
    @54
    wceq
    @49
    @50
    @10
    @40
    @42
    @3
    @9
    @40
    @3
    @1
    @2
    @40
    @41
    3expb
    ancoms
    adantl
    cB
    @44
    c.x
    cR
    @20
    @6
    srgmulgass.b
    srgmulgass.m
    @52
    mulgnn0p1
    syl3anc
    eqcomd
    sylan9eqr
    eqtrd
    exp31
    a2d
    nn0ind
    expd
    3impib
    impcom
end
