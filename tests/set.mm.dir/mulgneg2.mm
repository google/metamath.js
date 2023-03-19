include "cgrp.mm"
include "wcel.mm"
include "cz.mm"
include "cneg.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "cc0.mm"
include "c1.mm"
include "caddc.mm"
include "wa.mm"
include "negeq.mm"
include "neg0.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "c0g.mm"
include "eqid.mm"
include "mulg0.mm"
include "adantl.mm"
include "grpinvcl.mm"
include "syl.mm"
include "eqtr4d.mm"
include "cn0.mm"
include "wi.mm"
include "cplusg.mm"
include "cc.mm"
include "nn0cn.mm"
include "ax-1cn.mm"
include "negdi.mm"
include "sylancl.mm"
include "simpll.mm"
include "nn0negz.mm"
include "1z.mm"
include "znegcl.mm"
include "mp1i.mm"
include "simplr.mm"
include "mulgdir.mm"
include "syl13anc.mm"
include "mulgm1.mm"
include "adantr.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "cmnd.mm"
include "grpmnd.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "mulgnn0p1.mm"
include "syl3anc.mm"
include "syl5ibr.mm"
include "ex.mm"
include "cn.mm"
include "fveq2.mm"
include "nnnegz.mm"
include "mulgneg.mm"
include "id.mm"
include "mulgnegnn.mm"
include "syl2anr.mm"
include "zindd.mm"
include "3impia.mm"
include "3com23.mm"

theorem mulgneg2
  let cB: class B
  let c.x: class .x.
  let cG: class G
  let cI: class I
  let cN: class N
  let cX: class X
  let vn: setvar n
  let vx: setvar x
  assume mulgneg2.b: |- B = ( Base ` G )
  assume mulgneg2.m: |- .x. = ( .g ` G )
  assume mulgneg2.i: |- I = ( invg ` G )


  assert |- ( ( G e. Grp /\ N e. ZZ /\ X e. B ) -> ( -u N .x. X ) = ( N .x. ( I ` X ) ) )

  proof
    cG
    cgrp
    wcel
    #
    cX
    cB
    wcel
    #
    cN
    cz
    wcel
    #
    cN
    cneg
    #
    cX
    c.x
    co
    #
    cN
    cX
    cI
    cfv
    #
    c.x
    co
    #
    wceq
    #
    @0
    @1
    @2
    @7
    vx
    cv
    #
    cneg
    #
    cX
    c.x
    co
    #
    @8
    @5
    c.x
    co
    #
    wceq
    cc0
    cX
    c.x
    co
    #
    cc0
    @5
    c.x
    co
    #
    wceq
    vn
    cv
    #
    cneg
    #
    cX
    c.x
    co
    #
    @14
    @5
    c.x
    co
    #
    wceq
    #
    @15
    cneg
    #
    cX
    c.x
    co
    #
    @15
    @5
    c.x
    co
    #
    wceq
    #
    @14
    c1
    caddc
    co
    #
    cneg
    #
    cX
    c.x
    co
    #
    @23
    @5
    c.x
    co
    #
    wceq
    #
    @7
    @0
    @1
    wa
    #
    vx
    vn
    cN
    @8
    cc0
    wceq
    #
    @10
    @12
    @11
    @13
    @29
    @9
    cc0
    cX
    c.x
    @29
    @9
    cc0
    cneg
    cc0
    @8
    cc0
    negeq
    neg0
    syl6eq
    oveq1d
    @8
    cc0
    @5
    c.x
    oveq1
    eqeq12d
    @8
    @14
    wceq
    #
    @10
    @16
    @11
    @17
    @30
    @9
    @15
    cX
    c.x
    @8
    @14
    negeq
    oveq1d
    @8
    @14
    @5
    c.x
    oveq1
    eqeq12d
    @8
    @23
    wceq
    #
    @10
    @25
    @11
    @26
    @31
    @9
    @24
    cX
    c.x
    @8
    @23
    negeq
    oveq1d
    @8
    @23
    @5
    c.x
    oveq1
    eqeq12d
    @8
    @15
    wceq
    #
    @10
    @20
    @11
    @21
    @32
    @9
    @19
    cX
    c.x
    @8
    @15
    negeq
    oveq1d
    @8
    @15
    @5
    c.x
    oveq1
    eqeq12d
    @8
    cN
    wceq
    #
    @10
    @4
    @11
    @6
    @33
    @9
    @3
    cX
    c.x
    @8
    cN
    negeq
    oveq1d
    @8
    cN
    @5
    c.x
    oveq1
    eqeq12d
    @28
    @12
    cG
    c0g
    cfv
    #
    @13
    @1
    @12
    @34
    wceq
    @0
    cB
    c.x
    cG
    cX
    @34
    mulgneg2.b
    @34
    eqid
    #
    mulgneg2.m
    mulg0
    adantl
    @28
    @5
    cB
    wcel
    #
    @13
    @34
    wceq
    cB
    cG
    cI
    cX
    mulgneg2.b
    mulgneg2.i
    grpinvcl
    #
    cB
    c.x
    cG
    @5
    @34
    mulgneg2.b
    @35
    mulgneg2.m
    mulg0
    syl
    eqtr4d
    @28
    @14
    cn0
    wcel
    #
    @18
    @27
    wi
    @18
    @27
    @28
    @38
    wa
    #
    @16
    @5
    cG
    cplusg
    cfv
    #
    co
    #
    @17
    @5
    @40
    co
    #
    wceq
    @16
    @17
    @5
    @40
    oveq1
    @39
    @25
    @41
    @26
    @42
    @39
    @25
    @15
    c1
    cneg
    #
    caddc
    co
    #
    cX
    c.x
    co
    #
    @16
    @43
    cX
    c.x
    co
    #
    @40
    co
    #
    @41
    @39
    @24
    @44
    cX
    c.x
    @39
    @14
    cc
    wcel
    #
    c1
    cc
    wcel
    @24
    @44
    wceq
    @38
    @48
    @28
    @14
    nn0cn
    adantl
    ax-1cn
    @14
    c1
    negdi
    sylancl
    oveq1d
    @39
    @0
    @15
    cz
    wcel
    #
    @43
    cz
    wcel
    #
    @1
    @45
    @47
    wceq
    @0
    @1
    @38
    simpll
    @38
    @49
    @28
    @14
    nn0negz
    adantl
    c1
    cz
    wcel
    @50
    @39
    1z
    c1
    znegcl
    mp1i
    @0
    @1
    @38
    simplr
    cB
    @40
    c.x
    cG
    @15
    @43
    cX
    mulgneg2.b
    mulgneg2.m
    @40
    eqid
    #
    mulgdir
    syl13anc
    @39
    @46
    @5
    @16
    @40
    @28
    @46
    @5
    wceq
    @38
    cB
    c.x
    cG
    cI
    cX
    mulgneg2.b
    mulgneg2.m
    mulgneg2.i
    mulgm1
    adantr
    oveq2d
    3eqtrd
    @39
    cG
    cmnd
    wcel
    #
    @38
    @36
    @26
    @42
    wceq
    @0
    @52
    @1
    @38
    cG
    grpmnd
    ad2antrr
    @28
    @38
    simpr
    @28
    @36
    @38
    @37
    adantr
    cB
    @40
    c.x
    cG
    @14
    @5
    mulgneg2.b
    mulgneg2.m
    @51
    mulgnn0p1
    syl3anc
    eqeq12d
    syl5ibr
    ex
    @28
    @14
    cn
    wcel
    #
    @18
    @22
    wi
    @18
    @22
    @28
    @53
    wa
    #
    @16
    cI
    cfv
    #
    @17
    cI
    cfv
    #
    wceq
    @16
    @17
    cI
    fveq2
    @54
    @20
    @55
    @21
    @56
    @54
    @0
    @49
    @1
    @20
    @55
    wceq
    @0
    @1
    @53
    simpll
    @53
    @49
    @28
    @14
    nnnegz
    adantl
    @0
    @1
    @53
    simplr
    cB
    c.x
    cG
    cI
    @15
    cX
    mulgneg2.b
    mulgneg2.m
    mulgneg2.i
    mulgneg
    syl3anc
    @53
    @53
    @36
    @21
    @56
    wceq
    @28
    @53
    id
    @37
    cB
    c.x
    cG
    cI
    @14
    @5
    mulgneg2.b
    mulgneg2.m
    mulgneg2.i
    mulgnegnn
    syl2anr
    eqeq12d
    syl5ibr
    ex
    zindd
    3impia
    3com23
end
