include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "csg.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "wne.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "cgrp.mm"
include "matgrp.mm"
include "adantr.mm"
include "dmatmat.mm"
include "imp.mm"
include "adantrr.mm"
include "adantrl.mm"
include "eqid.mm"
include "grpsubcl.mm"
include "syl3anc.mm"
include "simpr.mm"
include "anim12d.mm"
include "matsubgcell.mm"
include "w3a.mm"
include "simpll.mm"
include "simprl.mm"
include "3jca.mm"
include "simplrl.mm"
include "simplrr.mm"
include "dmatelnd.mm"
include "syl13anc.mm"
include "simprr.mm"
include "oveq12d.mm"
include "cbs.mm"
include "ringgrp.mm"
include "ring0cl.mm"
include "jca.mm"
include "adantl.mm"
include "grpsubid.mm"
include "syl.mm"
include "ad3antrrr.mm"
include "3eqtrd.mm"
include "ex.mm"
include "ralrimivva.mm"
include "wb.mm"
include "dmatel.mm"
include "mpbir2and.mm"

theorem dmatsubcl
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cN: class N
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vi: setvar i
  let vj: setvar j
  let cI: class I
  let cJ: class J
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume dmatid.a: |- A = ( N Mat R )
  assume dmatid.b: |- B = ( Base ` A )
  assume dmatid.0: |- .0. = ( 0g ` R )
  assume dmatid.d: |- D = ( N DMat R )


  assert |- ( ( ( N e. Fin /\ R e. Ring ) /\ ( X e. D /\ Y e. D ) ) -> ( X ( -g ` A ) Y ) e. D )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    #
    cX
    cD
    wcel
    #
    cY
    cD
    wcel
    #
    wa
    #
    wa
    #
    cX
    cY
    cA
    csg
    cfv
    #
    co
    #
    cD
    wcel
    #
    @8
    cB
    wcel
    #
    vi
    cv
    #
    vj
    cv
    #
    wne
    #
    @11
    @12
    @8
    co
    #
    c.0
    wceq
    #
    wi
    #
    vj
    cN
    wral
    vi
    cN
    wral
    #
    @6
    cA
    cgrp
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
    @10
    @2
    @18
    @5
    cA
    cR
    cN
    dmatid.a
    matgrp
    adantr
    @2
    @3
    @19
    @4
    @2
    @3
    @19
    cA
    cB
    cD
    cR
    cX
    cN
    crg
    c.0
    dmatid.a
    dmatid.b
    dmatid.0
    dmatid.d
    dmatmat
    #
    imp
    adantrr
    @2
    @4
    @20
    @3
    @2
    @4
    @20
    cA
    cB
    cD
    cR
    cY
    cN
    crg
    c.0
    dmatid.a
    dmatid.b
    dmatid.0
    dmatid.d
    dmatmat
    #
    imp
    adantrl
    cB
    cA
    @7
    cX
    cY
    dmatid.b
    @7
    eqid
    #
    grpsubcl
    syl3anc
    @6
    @16
    vi
    vj
    cN
    cN
    @6
    @11
    cN
    wcel
    #
    @12
    cN
    wcel
    #
    wa
    #
    wa
    #
    @13
    @15
    @27
    @13
    wa
    #
    @14
    @11
    @12
    cX
    co
    #
    @11
    @12
    cY
    co
    #
    cR
    csg
    cfv
    #
    co
    #
    c.0
    c.0
    @31
    co
    #
    c.0
    @27
    @14
    @32
    wceq
    #
    @13
    @27
    @1
    @19
    @20
    wa
    #
    @26
    @34
    @6
    @1
    @26
    @2
    @1
    @5
    @0
    @1
    simpr
    adantr
    #
    adantr
    @6
    @35
    @26
    @2
    @5
    @35
    @2
    @3
    @19
    @4
    @20
    @21
    @22
    anim12d
    imp
    adantr
    @6
    @26
    simpr
    cA
    cB
    cR
    @7
    @11
    @12
    @31
    cN
    cX
    cY
    dmatid.a
    dmatid.b
    @23
    @31
    eqid
    #
    matsubgcell
    syl3anc
    adantr
    @28
    @29
    c.0
    @30
    c.0
    @31
    @28
    @0
    @1
    @3
    w3a
    #
    @24
    @25
    @13
    @29
    c.0
    wceq
    @27
    @38
    @13
    @6
    @38
    @26
    @6
    @0
    @1
    @3
    @0
    @1
    @5
    simpll
    #
    @36
    @2
    @3
    @4
    simprl
    3jca
    adantr
    adantr
    @6
    @24
    @25
    @13
    simplrl
    #
    @6
    @24
    @25
    @13
    simplrr
    #
    @27
    @13
    simpr
    #
    cA
    cB
    cD
    cR
    @11
    @12
    cN
    cX
    c.0
    dmatid.a
    dmatid.b
    dmatid.0
    dmatid.d
    dmatelnd
    syl13anc
    @28
    @0
    @1
    @4
    w3a
    #
    @24
    @25
    @13
    @30
    c.0
    wceq
    @27
    @43
    @13
    @6
    @43
    @26
    @6
    @0
    @1
    @4
    @39
    @36
    @2
    @3
    @4
    simprr
    3jca
    adantr
    adantr
    @40
    @41
    @42
    cA
    cB
    cD
    cR
    @11
    @12
    cN
    cY
    c.0
    dmatid.a
    dmatid.b
    dmatid.0
    dmatid.d
    dmatelnd
    syl13anc
    oveq12d
    @2
    @33
    c.0
    wceq
    #
    @5
    @26
    @13
    @2
    cR
    cgrp
    wcel
    #
    c.0
    cR
    cbs
    cfv
    #
    wcel
    #
    wa
    #
    @44
    @1
    @48
    @0
    @1
    @45
    @47
    cR
    ringgrp
    @46
    cR
    c.0
    @46
    eqid
    #
    dmatid.0
    ring0cl
    jca
    adantl
    @46
    cR
    @31
    c.0
    c.0
    @49
    dmatid.0
    @37
    grpsubid
    syl
    ad3antrrr
    3eqtrd
    ex
    ralrimivva
    @2
    @9
    @10
    @17
    wa
    wb
    @5
    cA
    cB
    cD
    cR
    vi
    vj
    @8
    cN
    crg
    c.0
    dmatid.a
    dmatid.b
    dmatid.0
    dmatid.d
    dmatel
    adantr
    mpbir2and
end
