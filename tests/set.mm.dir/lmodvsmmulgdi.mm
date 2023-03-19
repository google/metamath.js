include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "clmod.mm"
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
include "lmod0vs.mm"
include "syl2anc.mm"
include "simpl.mm"
include "mulg0.mm"
include "syl.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "3eqtr4rd.mm"
include "cplusg.mm"
include "cmnd.mm"
include "cgrp.mm"
include "lmodgrp.mm"
include "grpmnd.mm"
include "adantl.mm"
include "mulgnn0p1.mm"
include "crg.mm"
include "lmodring.mm"
include "ringmnd.mm"
include "simprll.mm"
include "mulgnn0cl.mm"
include "lmodvsdir.mm"
include "syl13anc.mm"
include "eqcomd.mm"
include "eqtr3d.mm"
include "sylan9eqr.mm"
include "eqtrd.mm"
include "exp31.mm"
include "a2d.mm"
include "nn0ind.mm"
include "exp4c.mm"
include "com12.mm"
include "3imp.mm"
include "impcom.mm"

theorem lmodvsmmulgdi
  let cC: class C
  let c.x: class .x.
  let cE: class E
  let c.ex: class .^
  let cF: class F
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume lmodvsmmulgdi.v: |- V = ( Base ` W )
  assume lmodvsmmulgdi.f: |- F = ( Scalar ` W )
  assume lmodvsmmulgdi.s: |- .x. = ( .s ` W )
  assume lmodvsmmulgdi.k: |- K = ( Base ` F )
  assume lmodvsmmulgdi.p: |- .^ = ( .g ` W )
  assume lmodvsmmulgdi.e: |- E = ( .g ` F )


  assert |- ( ( W e. LMod /\ ( C e. K /\ N e. NN0 /\ X e. V ) ) -> ( N .^ ( C .x. X ) ) = ( ( N E C ) .x. X ) )

  proof
    cC
    cK
    wcel
    #
    cN
    cn0
    wcel
    #
    cX
    cV
    wcel
    #
    w3a
    cW
    clmod
    wcel
    #
    cN
    cC
    cX
    c.x
    co
    #
    c.ex
    co
    #
    cN
    cC
    cE
    co
    #
    cX
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
    #
    @1
    @0
    @2
    @9
    wi
    @1
    @0
    @2
    @3
    @8
    @0
    @2
    wa
    #
    @3
    wa
    #
    vx
    cv
    #
    @4
    c.ex
    co
    #
    @12
    cC
    cE
    co
    #
    cX
    c.x
    co
    #
    wceq
    #
    wi
    @11
    cc0
    @4
    c.ex
    co
    #
    cc0
    cC
    cE
    co
    #
    cX
    c.x
    co
    #
    wceq
    #
    wi
    @11
    vy
    cv
    #
    @4
    c.ex
    co
    #
    @21
    cC
    cE
    co
    #
    cX
    c.x
    co
    #
    wceq
    #
    wi
    @11
    @21
    c1
    caddc
    co
    #
    @4
    c.ex
    co
    #
    @26
    cC
    cE
    co
    #
    cX
    c.x
    co
    #
    wceq
    #
    wi
    @11
    @8
    wi
    vx
    vy
    cN
    @12
    cc0
    wceq
    #
    @16
    @20
    @11
    @31
    @13
    @17
    @15
    @19
    @12
    cc0
    @4
    c.ex
    oveq1
    @31
    @14
    @18
    cX
    c.x
    @12
    cc0
    cC
    cE
    oveq1
    oveq1d
    eqeq12d
    imbi2d
    vx
    vy
    weq
    #
    @16
    @25
    @11
    @32
    @13
    @22
    @15
    @24
    @12
    @21
    @4
    c.ex
    oveq1
    @32
    @14
    @23
    cX
    c.x
    @12
    @21
    cC
    cE
    oveq1
    oveq1d
    eqeq12d
    imbi2d
    @12
    @26
    wceq
    #
    @16
    @30
    @11
    @33
    @13
    @27
    @15
    @29
    @12
    @26
    @4
    c.ex
    oveq1
    @33
    @14
    @28
    cX
    c.x
    @12
    @26
    cC
    cE
    oveq1
    oveq1d
    eqeq12d
    imbi2d
    @12
    cN
    wceq
    #
    @16
    @8
    @11
    @34
    @13
    @5
    @15
    @7
    @12
    cN
    @4
    c.ex
    oveq1
    @34
    @14
    @6
    cX
    c.x
    @12
    cN
    cC
    cE
    oveq1
    oveq1d
    eqeq12d
    imbi2d
    @11
    cF
    c0g
    cfv
    #
    cX
    c.x
    co
    #
    cW
    c0g
    cfv
    #
    @19
    @17
    @11
    @3
    @2
    @36
    @37
    wceq
    @10
    @3
    simpr
    #
    @10
    @2
    @3
    @0
    @2
    simpr
    adantr
    #
    c.x
    cF
    @35
    cV
    cW
    cX
    @37
    lmodvsmmulgdi.v
    lmodvsmmulgdi.f
    lmodvsmmulgdi.s
    @35
    eqid
    #
    @37
    eqid
    #
    lmod0vs
    syl2anc
    @11
    @18
    @35
    cX
    c.x
    @11
    @0
    @18
    @35
    wceq
    @10
    @0
    @3
    @0
    @2
    simpl
    adantr
    #
    cK
    cE
    cF
    cC
    @35
    lmodvsmmulgdi.k
    @40
    lmodvsmmulgdi.e
    mulg0
    syl
    oveq1d
    @11
    @4
    cV
    wcel
    #
    @17
    @37
    wceq
    @11
    @3
    @0
    @2
    @43
    @38
    @42
    @39
    cC
    c.x
    cF
    cK
    cV
    cW
    cX
    lmodvsmmulgdi.v
    lmodvsmmulgdi.f
    lmodvsmmulgdi.s
    lmodvsmmulgdi.k
    lmodvscl
    syl3anc
    #
    cV
    c.ex
    cW
    @4
    @37
    lmodvsmmulgdi.v
    @41
    lmodvsmmulgdi.p
    mulg0
    syl
    3eqtr4rd
    @21
    cn0
    wcel
    #
    @11
    @25
    @30
    @45
    @11
    @25
    @30
    @45
    @11
    wa
    #
    @25
    wa
    @27
    @22
    @4
    cW
    cplusg
    cfv
    #
    co
    #
    @29
    @46
    @27
    @48
    wceq
    #
    @25
    @46
    cW
    cmnd
    wcel
    #
    @45
    @43
    @49
    @11
    @50
    @45
    @3
    @50
    @10
    @3
    cW
    cgrp
    wcel
    @50
    cW
    lmodgrp
    cW
    grpmnd
    syl
    adantl
    adantl
    @45
    @11
    simpl
    #
    @11
    @43
    @45
    @44
    adantl
    cV
    @47
    c.ex
    cW
    @21
    @4
    lmodvsmmulgdi.v
    lmodvsmmulgdi.p
    @47
    eqid
    #
    mulgnn0p1
    syl3anc
    adantr
    @25
    @46
    @48
    @24
    @4
    @47
    co
    #
    @29
    @22
    @24
    @4
    @47
    oveq1
    @46
    @23
    cC
    cF
    cplusg
    cfv
    #
    co
    #
    cX
    c.x
    co
    #
    @53
    @29
    @46
    @3
    @23
    cK
    wcel
    #
    @0
    @2
    @56
    @53
    wceq
    @11
    @3
    @45
    @38
    adantl
    @46
    cF
    cmnd
    wcel
    #
    @45
    @0
    @57
    @11
    @58
    @45
    @3
    @58
    @10
    @3
    cF
    crg
    wcel
    @58
    cF
    cW
    lmodvsmmulgdi.f
    lmodring
    cF
    ringmnd
    syl
    adantl
    adantl
    #
    @51
    @45
    @0
    @2
    @3
    simprll
    #
    cK
    cE
    cF
    @21
    cC
    lmodvsmmulgdi.k
    lmodvsmmulgdi.e
    mulgnn0cl
    syl3anc
    @60
    @11
    @2
    @45
    @39
    adantl
    @47
    @54
    @23
    cC
    c.x
    cF
    cK
    cV
    cW
    cX
    lmodvsmmulgdi.v
    @52
    lmodvsmmulgdi.f
    lmodvsmmulgdi.s
    lmodvsmmulgdi.k
    @54
    eqid
    #
    lmodvsdir
    syl13anc
    @46
    @55
    @28
    cX
    c.x
    @46
    @28
    @55
    @46
    @58
    @45
    @0
    @28
    @55
    wceq
    @59
    @51
    @60
    cK
    @54
    cE
    cF
    @21
    cC
    lmodvsmmulgdi.k
    lmodvsmmulgdi.e
    @61
    mulgnn0p1
    syl3anc
    eqcomd
    oveq1d
    eqtr3d
    sylan9eqr
    eqtrd
    exp31
    a2d
    nn0ind
    exp4c
    com12
    3imp
    impcom
end
