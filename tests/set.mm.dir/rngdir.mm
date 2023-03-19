include "crng.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "cabl.mm"
include "cmgp.mm"
include "cfv.mm"
include "csgrp.mm"
include "cv.mm"
include "wa.mm"
include "wral.mm"
include "wi.mm"
include "eqid.mm"
include "isrng.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "oveq1d.mm"
include "anbi12d.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "rspc3v.mm"
include "simpr.mm"
include "syl6com.mm"
include "3ad2ant3.mm"
include "sylbi.mm"
include "imp.mm"

theorem rngdir
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vk: setvar k
  let vx: setvar x
  assume rngdi.b: |- B = ( Base ` R )
  assume rngdi.p: |- .+ = ( +g ` R )
  assume rngdi.t: |- .x. = ( .r ` R )


  assert |- ( ( R e. Rng /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X .+ Y ) .x. Z ) = ( ( X .x. Z ) .+ ( Y .x. Z ) ) )

  proof
    cR
    crng
    wcel
    #
    cX
    cB
    wcel
    cY
    cB
    wcel
    cZ
    cB
    wcel
    w3a
    #
    cX
    cY
    c.pl
    co
    #
    cZ
    c.x
    co
    #
    cX
    cZ
    c.x
    co
    #
    cY
    cZ
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    @0
    cR
    cabl
    wcel
    #
    cR
    cmgp
    cfv
    #
    csgrp
    wcel
    #
    va
    cv
    #
    vb
    cv
    #
    vc
    cv
    #
    c.pl
    co
    #
    c.x
    co
    #
    @11
    @12
    c.x
    co
    #
    @11
    @13
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    @11
    @12
    c.pl
    co
    #
    @13
    c.x
    co
    #
    @17
    @12
    @13
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    wa
    #
    vc
    cB
    wral
    vb
    cB
    wral
    va
    cB
    wral
    #
    w3a
    @1
    @7
    wi
    #
    va
    vb
    vc
    cB
    c.pl
    cR
    c.x
    @9
    rngdi.b
    @9
    eqid
    rngdi.p
    rngdi.t
    isrng
    @26
    @8
    @27
    @10
    @1
    @26
    cX
    cY
    cZ
    c.pl
    co
    #
    c.x
    co
    #
    cX
    cY
    c.x
    co
    #
    @4
    c.pl
    co
    #
    wceq
    #
    @7
    wa
    #
    @7
    @25
    @33
    cX
    @14
    c.x
    co
    #
    cX
    @12
    c.x
    co
    #
    cX
    @13
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    cX
    @12
    c.pl
    co
    #
    @13
    c.x
    co
    #
    @36
    @22
    c.pl
    co
    #
    wceq
    #
    wa
    cX
    cY
    @13
    c.pl
    co
    #
    c.x
    co
    #
    @30
    @36
    c.pl
    co
    #
    wceq
    #
    @2
    @13
    c.x
    co
    #
    @36
    cY
    @13
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    wa
    va
    vb
    vc
    cX
    cY
    cZ
    cB
    cB
    cB
    @11
    cX
    wceq
    #
    @19
    @38
    @24
    @42
    @51
    @15
    @34
    @18
    @37
    @11
    cX
    @14
    c.x
    oveq1
    @51
    @16
    @35
    @17
    @36
    c.pl
    @11
    cX
    @12
    c.x
    oveq1
    @11
    cX
    @13
    c.x
    oveq1
    #
    oveq12d
    eqeq12d
    @51
    @21
    @40
    @23
    @41
    @51
    @20
    @39
    @13
    c.x
    @11
    cX
    @12
    c.pl
    oveq1
    oveq1d
    @51
    @17
    @36
    @22
    c.pl
    @52
    oveq1d
    eqeq12d
    anbi12d
    @12
    cY
    wceq
    #
    @38
    @46
    @42
    @50
    @53
    @34
    @44
    @37
    @45
    @53
    @14
    @43
    cX
    c.x
    @12
    cY
    @13
    c.pl
    oveq1
    oveq2d
    @53
    @35
    @30
    @36
    c.pl
    @12
    cY
    cX
    c.x
    oveq2
    oveq1d
    eqeq12d
    @53
    @40
    @47
    @41
    @49
    @53
    @39
    @2
    @13
    c.x
    @12
    cY
    cX
    c.pl
    oveq2
    oveq1d
    @53
    @22
    @48
    @36
    c.pl
    @12
    cY
    @13
    c.x
    oveq1
    oveq2d
    eqeq12d
    anbi12d
    @13
    cZ
    wceq
    #
    @46
    @32
    @50
    @7
    @54
    @44
    @29
    @45
    @31
    @54
    @43
    @28
    cX
    c.x
    @13
    cZ
    cY
    c.pl
    oveq2
    oveq2d
    @54
    @36
    @4
    @30
    c.pl
    @13
    cZ
    cX
    c.x
    oveq2
    #
    oveq2d
    eqeq12d
    @54
    @47
    @3
    @49
    @6
    @13
    cZ
    @2
    c.x
    oveq2
    @54
    @36
    @4
    @48
    @5
    c.pl
    @55
    @13
    cZ
    cY
    c.x
    oveq2
    oveq12d
    eqeq12d
    anbi12d
    rspc3v
    @32
    @7
    simpr
    syl6com
    3ad2ant3
    sylbi
    imp
end
