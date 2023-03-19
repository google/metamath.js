include "cgrp.mm"
include "wcel.mm"
include "cz.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "cv.mm"
include "cc0.mm"
include "cneg.mm"
include "c1.mm"
include "caddc.mm"
include "wa.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "weq.mm"
include "c0g.mm"
include "eqid.mm"
include "grpinvid.mm"
include "eqcomd.mm"
include "adantr.mm"
include "grpinvcl.mm"
include "mulg0.mm"
include "syl.mm"
include "adantl.mm"
include "3eqtr4d.mm"
include "cn0.mm"
include "w3a.mm"
include "cplusg.mm"
include "oveq2.mm"
include "cmnd.mm"
include "grpmnd.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "3adant2.mm"
include "mulgnn0p1.mm"
include "syl3anc.mm"
include "simp1.mm"
include "nn0z.mm"
include "3ad2ant2.mm"
include "mulgaddcom.mm"
include "eqtrd.mm"
include "syl3an1.mm"
include "mulgcl.mm"
include "syl3an2.mm"
include "grpinvadd.mm"
include "syld3an2.mm"
include "3exp1.mm"
include "com23.mm"
include "imp.mm"
include "cn.mm"
include "nnz.mm"
include "mulgneg.mm"
include "syld3an3.mm"
include "simpr.mm"
include "eqtr4d.mm"
include "syl5.mm"
include "zindd.mm"
include "ex.mm"
include "3imp.mm"

theorem mulginvcom
  let cB: class B
  let c.x: class .x.
  let cG: class G
  let cI: class I
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume mulginvcom.b: |- B = ( Base ` G )
  assume mulginvcom.t: |- .x. = ( .g ` G )
  assume mulginvcom.i: |- I = ( invg ` G )


  assert |- ( ( G e. Grp /\ N e. ZZ /\ X e. B ) -> ( N .x. ( I ` X ) ) = ( I ` ( N .x. X ) ) )

  proof
    cG
    cgrp
    wcel
    #
    cN
    cz
    wcel
    #
    cX
    cB
    wcel
    #
    cN
    cX
    cI
    cfv
    #
    c.x
    co
    #
    cN
    cX
    c.x
    co
    #
    cI
    cfv
    #
    wceq
    #
    @0
    @2
    @1
    @7
    @0
    @2
    @1
    @7
    wi
    vx
    cv
    #
    @3
    c.x
    co
    #
    @8
    cX
    c.x
    co
    #
    cI
    cfv
    #
    wceq
    cc0
    @3
    c.x
    co
    #
    cc0
    cX
    c.x
    co
    #
    cI
    cfv
    #
    wceq
    vy
    cv
    #
    @3
    c.x
    co
    #
    @15
    cX
    c.x
    co
    #
    cI
    cfv
    #
    wceq
    #
    @15
    cneg
    #
    @3
    c.x
    co
    #
    @20
    cX
    c.x
    co
    #
    cI
    cfv
    #
    wceq
    #
    @15
    c1
    caddc
    co
    #
    @3
    c.x
    co
    #
    @25
    cX
    c.x
    co
    #
    cI
    cfv
    #
    wceq
    #
    @7
    @0
    @2
    wa
    #
    vx
    vy
    cN
    @8
    cc0
    wceq
    #
    @9
    @12
    @11
    @14
    @8
    cc0
    @3
    c.x
    oveq1
    @31
    @10
    @13
    cI
    @8
    cc0
    cX
    c.x
    oveq1
    fveq2d
    eqeq12d
    vx
    vy
    weq
    #
    @9
    @16
    @11
    @18
    @8
    @15
    @3
    c.x
    oveq1
    @32
    @10
    @17
    cI
    @8
    @15
    cX
    c.x
    oveq1
    fveq2d
    eqeq12d
    @8
    @25
    wceq
    #
    @9
    @26
    @11
    @28
    @8
    @25
    @3
    c.x
    oveq1
    @33
    @10
    @27
    cI
    @8
    @25
    cX
    c.x
    oveq1
    fveq2d
    eqeq12d
    @8
    @20
    wceq
    #
    @9
    @21
    @11
    @23
    @8
    @20
    @3
    c.x
    oveq1
    @34
    @10
    @22
    cI
    @8
    @20
    cX
    c.x
    oveq1
    fveq2d
    eqeq12d
    @8
    cN
    wceq
    #
    @9
    @4
    @11
    @6
    @8
    cN
    @3
    c.x
    oveq1
    @35
    @10
    @5
    cI
    @8
    cN
    cX
    c.x
    oveq1
    fveq2d
    eqeq12d
    @30
    cG
    c0g
    cfv
    #
    @36
    cI
    cfv
    #
    @12
    @14
    @0
    @36
    @37
    wceq
    @2
    @0
    @37
    @36
    cG
    cI
    @36
    @36
    eqid
    #
    mulginvcom.i
    grpinvid
    eqcomd
    adantr
    @30
    @3
    cB
    wcel
    #
    @12
    @36
    wceq
    cB
    cG
    cI
    cX
    mulginvcom.b
    mulginvcom.i
    grpinvcl
    #
    cB
    c.x
    cG
    @3
    @36
    mulginvcom.b
    @38
    mulginvcom.t
    mulg0
    syl
    @30
    @13
    @36
    cI
    @2
    @13
    @36
    wceq
    @0
    cB
    c.x
    cG
    cX
    @36
    mulginvcom.b
    @38
    mulginvcom.t
    mulg0
    adantl
    fveq2d
    3eqtr4d
    @0
    @2
    @15
    cn0
    wcel
    #
    @19
    @29
    wi
    #
    wi
    @0
    @41
    @2
    @42
    @0
    @41
    @2
    @19
    @29
    @0
    @41
    @2
    w3a
    #
    @19
    wa
    @3
    @16
    cG
    cplusg
    cfv
    #
    co
    #
    @3
    @18
    @44
    co
    #
    @26
    @28
    @19
    @45
    @46
    wceq
    @43
    @16
    @18
    @3
    @44
    oveq2
    adantl
    @43
    @26
    @45
    wceq
    @19
    @43
    @26
    @16
    @3
    @44
    co
    #
    @45
    @43
    cG
    cmnd
    wcel
    #
    @41
    @39
    @26
    @47
    wceq
    @0
    @41
    @48
    @2
    cG
    grpmnd
    #
    3ad2ant1
    @0
    @41
    @2
    simp2
    @0
    @2
    @39
    @41
    @40
    3adant2
    #
    cB
    @44
    c.x
    cG
    @15
    @3
    mulginvcom.b
    mulginvcom.t
    @44
    eqid
    #
    mulgnn0p1
    syl3anc
    @43
    @0
    @15
    cz
    wcel
    #
    @39
    @47
    @45
    wceq
    @0
    @41
    @2
    simp1
    @41
    @0
    @52
    @2
    @15
    nn0z
    #
    3ad2ant2
    @50
    cB
    @44
    c.x
    cG
    @15
    @3
    mulginvcom.b
    mulginvcom.t
    @51
    mulgaddcom
    syl3anc
    eqtrd
    adantr
    @43
    @28
    @46
    wceq
    @19
    @43
    @28
    @17
    cX
    @44
    co
    #
    cI
    cfv
    #
    @46
    @43
    @27
    @54
    cI
    @0
    @48
    @41
    @2
    @27
    @54
    wceq
    @49
    cB
    @44
    c.x
    cG
    @15
    cX
    mulginvcom.b
    mulginvcom.t
    @51
    mulgnn0p1
    syl3an1
    fveq2d
    @0
    @17
    cB
    wcel
    #
    @41
    @2
    @55
    @46
    wceq
    @41
    @0
    @52
    @2
    @56
    @53
    cB
    c.x
    cG
    @15
    cX
    mulginvcom.b
    mulginvcom.t
    mulgcl
    syl3an2
    cB
    @44
    cG
    cI
    @17
    cX
    mulginvcom.b
    @51
    mulginvcom.i
    grpinvadd
    syld3an2
    eqtrd
    adantr
    3eqtr4d
    3exp1
    com23
    imp
    @15
    cn
    wcel
    @52
    @30
    @19
    @24
    wi
    #
    @15
    nnz
    @0
    @2
    @52
    @57
    wi
    @0
    @52
    @2
    @57
    @0
    @52
    @2
    @19
    @24
    @0
    @52
    @2
    w3a
    #
    @19
    wa
    #
    @21
    @16
    cI
    cfv
    #
    @23
    @58
    @21
    @60
    wceq
    #
    @19
    @0
    @52
    @2
    @39
    @61
    @0
    @2
    @39
    @52
    @40
    3adant2
    cB
    c.x
    cG
    cI
    @15
    @3
    mulginvcom.b
    mulginvcom.t
    mulginvcom.i
    mulgneg
    syld3an3
    adantr
    @59
    @22
    @16
    cI
    @59
    @22
    @18
    @16
    @58
    @22
    @18
    wceq
    @19
    cB
    c.x
    cG
    cI
    @15
    cX
    mulginvcom.b
    mulginvcom.t
    mulginvcom.i
    mulgneg
    adantr
    @58
    @19
    simpr
    eqtr4d
    fveq2d
    eqtr4d
    3exp1
    com23
    imp
    syl5
    zindd
    ex
    com23
    3imp
end
