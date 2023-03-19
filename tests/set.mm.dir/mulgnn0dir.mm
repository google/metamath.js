include "cmnd.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "wa.mm"
include "cn.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "csgrp.mm"
include "mndsgrp.mm"
include "adantr.mm"
include "simplr.mm"
include "simpr.mm"
include "simpr3.mm"
include "ad2antrr.mm"
include "mulgnndir.mm"
include "syl13anc.mm"
include "c0g.mm"
include "cfv.mm"
include "simpll.mm"
include "simpr1.mm"
include "simplr3.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "eqid.mm"
include "mndrid.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "mulg0.mm"
include "syl.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "nn0cnd.mm"
include "addid1d.mm"
include "3eqtr4rd.mm"
include "adantlr.mm"
include "wo.mm"
include "simpr2.mm"
include "elnn0.mm"
include "sylib.mm"
include "mpjaodan.mm"
include "simplr2.mm"
include "mndlid.mm"
include "addid2d.mm"

theorem mulgnn0dir
  let cB: class B
  let c.pl: class .+
  let c.x: class .x.
  let cG: class G
  let cM: class M
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume mulgnndir.b: |- B = ( Base ` G )
  assume mulgnndir.t: |- .x. = ( .g ` G )
  assume mulgnndir.p: |- .+ = ( +g ` G )


  assert |- ( ( G e. Mnd /\ ( M e. NN0 /\ N e. NN0 /\ X e. B ) ) -> ( ( M + N ) .x. X ) = ( ( M .x. X ) .+ ( N .x. X ) ) )

  proof
    cG
    cmnd
    wcel
    #
    cM
    cn0
    wcel
    #
    cN
    cn0
    wcel
    #
    cX
    cB
    wcel
    #
    w3a
    #
    wa
    #
    cM
    cn
    wcel
    #
    cM
    cN
    caddc
    co
    #
    cX
    c.x
    co
    #
    cM
    cX
    c.x
    co
    #
    cN
    cX
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    cM
    cc0
    wceq
    #
    @5
    @6
    wa
    #
    cN
    cn
    wcel
    #
    @12
    cN
    cc0
    wceq
    #
    @14
    @15
    wa
    cG
    csgrp
    wcel
    #
    @6
    @15
    @3
    @12
    @14
    @17
    @15
    @5
    @17
    @6
    @0
    @17
    @4
    cG
    mndsgrp
    adantr
    adantr
    adantr
    @5
    @6
    @15
    simplr
    @14
    @15
    simpr
    @5
    @3
    @6
    @15
    @0
    @1
    @2
    @3
    simpr3
    ad2antrr
    cB
    c.pl
    c.x
    cG
    cM
    cN
    cX
    mulgnndir.b
    mulgnndir.t
    mulgnndir.p
    mulgnndir
    syl13anc
    @5
    @16
    @12
    @6
    @5
    @16
    wa
    #
    @9
    cG
    c0g
    cfv
    #
    c.pl
    co
    #
    @9
    @11
    @8
    @18
    @0
    @9
    cB
    wcel
    #
    @20
    @9
    wceq
    @0
    @4
    @16
    simpll
    #
    @18
    @0
    @1
    @3
    @21
    @22
    @5
    @1
    @16
    @0
    @1
    @2
    @3
    simpr1
    #
    adantr
    #
    @1
    @2
    @3
    @0
    @16
    simplr3
    #
    cB
    c.x
    cG
    cM
    cX
    mulgnndir.b
    mulgnndir.t
    mulgnn0cl
    syl3anc
    cB
    c.pl
    cG
    @9
    @19
    mulgnndir.b
    mulgnndir.p
    @19
    eqid
    #
    mndrid
    syl2anc
    @18
    @10
    @19
    @9
    c.pl
    @18
    @10
    cc0
    cX
    c.x
    co
    #
    @19
    @18
    cN
    cc0
    cX
    c.x
    @5
    @16
    simpr
    #
    oveq1d
    @18
    @3
    @27
    @19
    wceq
    #
    @25
    cB
    c.x
    cG
    cX
    @19
    mulgnndir.b
    @26
    mulgnndir.t
    mulg0
    #
    syl
    eqtrd
    oveq2d
    @18
    @7
    cM
    cX
    c.x
    @18
    @7
    cM
    cc0
    caddc
    co
    cM
    @18
    cN
    cc0
    cM
    caddc
    @28
    oveq2d
    @18
    cM
    @18
    cM
    @24
    nn0cnd
    addid1d
    eqtrd
    oveq1d
    3eqtr4rd
    adantlr
    @5
    @15
    @16
    wo
    #
    @6
    @5
    @2
    @31
    @0
    @1
    @2
    @3
    simpr2
    cN
    elnn0
    sylib
    adantr
    mpjaodan
    @5
    @13
    wa
    #
    @19
    @10
    c.pl
    co
    #
    @10
    @11
    @8
    @32
    @0
    @10
    cB
    wcel
    #
    @33
    @10
    wceq
    @0
    @4
    @13
    simpll
    #
    @32
    @0
    @2
    @3
    @34
    @35
    @1
    @2
    @3
    @0
    @13
    simplr2
    #
    @1
    @2
    @3
    @0
    @13
    simplr3
    #
    cB
    c.x
    cG
    cN
    cX
    mulgnndir.b
    mulgnndir.t
    mulgnn0cl
    syl3anc
    cB
    c.pl
    cG
    @10
    @19
    mulgnndir.b
    mulgnndir.p
    @26
    mndlid
    syl2anc
    @32
    @9
    @19
    @10
    c.pl
    @32
    @9
    @27
    @19
    @32
    cM
    cc0
    cX
    c.x
    @5
    @13
    simpr
    #
    oveq1d
    @32
    @3
    @29
    @37
    @30
    syl
    eqtrd
    oveq1d
    @32
    @7
    cN
    cX
    c.x
    @32
    @7
    cc0
    cN
    caddc
    co
    cN
    @32
    cM
    cc0
    cN
    caddc
    @38
    oveq1d
    @32
    cN
    @32
    cN
    @36
    nn0cnd
    addid2d
    eqtrd
    oveq1d
    3eqtr4rd
    @5
    @1
    @6
    @13
    wo
    @23
    cM
    elnn0
    sylib
    mpjaodan
end
