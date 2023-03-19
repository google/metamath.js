include "cmnd.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "wa.mm"
include "cn.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "csgrp.mm"
include "mndsgrp.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "simpr3.mm"
include "mulgnnass.mm"
include "syl13anc.mm"
include "expr.mm"
include "c0g.mm"
include "cfv.mm"
include "eqid.mm"
include "mulg0.mm"
include "syl.mm"
include "simpr1.mm"
include "nn0cnd.mm"
include "mul01d.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "mulgnn0z.mm"
include "3ad2antr1.mm"
include "eqtrd.mm"
include "3eqtr4d.mm"
include "oveq2.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "wo.mm"
include "simpr2.mm"
include "elnn0.mm"
include "sylib.mm"
include "mpjaod.mm"
include "ex.mm"
include "mul02d.mm"
include "mulgnn0cl.mm"
include "3adant3r1.mm"

theorem mulgnn0ass
  let cB: class B
  let c.x: class .x.
  let cG: class G
  let cM: class M
  let cN: class N
  let cX: class X
  let vm: setvar m
  let vn: setvar n
  assume mulgass.b: |- B = ( Base ` G )
  assume mulgass.t: |- .x. = ( .g ` G )


  assert |- ( ( G e. Mnd /\ ( M e. NN0 /\ N e. NN0 /\ X e. B ) ) -> ( ( M x. N ) .x. X ) = ( M .x. ( N .x. X ) ) )

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
    cmul
    co
    #
    cX
    c.x
    co
    #
    cM
    cN
    cX
    c.x
    co
    #
    c.x
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
    @11
    @5
    @6
    wa
    #
    cN
    cn
    wcel
    #
    @11
    cN
    cc0
    wceq
    #
    @5
    @6
    @14
    @11
    @5
    @6
    @14
    wa
    #
    wa
    cG
    csgrp
    wcel
    #
    @6
    @14
    @3
    @11
    @5
    @17
    @16
    @0
    @17
    @4
    cG
    mndsgrp
    adantr
    adantr
    @5
    @6
    @14
    simprl
    @5
    @6
    @14
    simprr
    @5
    @3
    @16
    @0
    @1
    @2
    @3
    simpr3
    #
    adantr
    cB
    c.x
    cG
    cM
    cN
    cX
    mulgass.b
    mulgass.t
    mulgnnass
    syl13anc
    expr
    @13
    @11
    @15
    cM
    cc0
    cmul
    co
    #
    cX
    c.x
    co
    #
    cM
    cc0
    cX
    c.x
    co
    #
    c.x
    co
    #
    wceq
    #
    @5
    @23
    @6
    @5
    @21
    cG
    c0g
    cfv
    #
    @20
    @22
    @5
    @3
    @21
    @24
    wceq
    @18
    cB
    c.x
    cG
    cX
    @24
    mulgass.b
    @24
    eqid
    #
    mulgass.t
    mulg0
    syl
    #
    @5
    @19
    cc0
    cX
    c.x
    @5
    cM
    @5
    cM
    @0
    @1
    @2
    @3
    simpr1
    #
    nn0cnd
    mul01d
    oveq1d
    @5
    @22
    cM
    @24
    c.x
    co
    #
    @24
    @5
    @21
    @24
    cM
    c.x
    @26
    oveq2d
    @0
    @2
    @1
    @28
    @24
    wceq
    @3
    cB
    c.x
    cG
    cM
    @24
    mulgass.b
    mulgass.t
    @25
    mulgnn0z
    3ad2antr1
    eqtrd
    3eqtr4d
    adantr
    @15
    @8
    @20
    @10
    @22
    @15
    @7
    @19
    cX
    c.x
    cN
    cc0
    cM
    cmul
    oveq2
    oveq1d
    @15
    @9
    @21
    cM
    c.x
    cN
    cc0
    cX
    c.x
    oveq1
    oveq2d
    eqeq12d
    syl5ibrcom
    @5
    @14
    @15
    wo
    #
    @6
    @5
    @2
    @29
    @0
    @1
    @2
    @3
    simpr2
    #
    cN
    elnn0
    sylib
    adantr
    mpjaod
    ex
    @5
    @11
    @12
    cc0
    cN
    cmul
    co
    #
    cX
    c.x
    co
    #
    cc0
    @9
    c.x
    co
    #
    wceq
    @5
    @21
    @24
    @32
    @33
    @26
    @5
    @31
    cc0
    cX
    c.x
    @5
    cN
    @5
    cN
    @30
    nn0cnd
    mul02d
    oveq1d
    @5
    @9
    cB
    wcel
    #
    @33
    @24
    wceq
    @0
    @2
    @3
    @34
    @1
    cB
    c.x
    cG
    cN
    cX
    mulgass.b
    mulgass.t
    mulgnn0cl
    3adant3r1
    cB
    c.x
    cG
    @9
    @24
    mulgass.b
    @25
    mulgass.t
    mulg0
    syl
    3eqtr4d
    @12
    @8
    @32
    @10
    @33
    @12
    @7
    @31
    cX
    c.x
    cM
    cc0
    cN
    cmul
    oveq1
    oveq1d
    cM
    cc0
    @9
    c.x
    oveq1
    eqeq12d
    syl5ibrcom
    @5
    @1
    @6
    @12
    wo
    @27
    cM
    elnn0
    sylib
    mpjaod
end
