include "ccmn.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "wa.mm"
include "cn.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "c1.mm"
include "cseq.mm"
include "cfv.mm"
include "cmnd.mm"
include "cv.mm"
include "cmnmnd.mm"
include "ad2antrr.mm"
include "mndcl.mm"
include "3expb.mm"
include "sylan.mm"
include "simpll.mm"
include "cmncom.mm"
include "mndass.mm"
include "cuz.mm"
include "simpr.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "cfz.mm"
include "simplr2.mm"
include "elfznn.mm"
include "fvconst2g.mm"
include "syl2an.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "simplr3.mm"
include "syl3anc.mm"
include "oveq12d.mm"
include "eqtr4d.mm"
include "seqcaopr.mm"
include "eqid.mm"
include "mulgnn.mm"
include "syl2anc.mm"
include "3eqtr4d.mm"
include "c0g.mm"
include "mulg0.mm"
include "syl.mm"
include "cbs.mm"
include "mndidcl.mm"
include "mndlid.mm"
include "mpdan.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "wo.mm"
include "simpr1.mm"
include "elnn0.mm"
include "sylib.mm"
include "mpjaodan.mm"

theorem mulgnn0di
  let cB: class B
  let c.pl: class .+
  let c.x: class .x.
  let cG: class G
  let cM: class M
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume mulgdi.b: |- B = ( Base ` G )
  assume mulgdi.m: |- .x. = ( .g ` G )
  assume mulgdi.p: |- .+ = ( +g ` G )


  assert |- ( ( G e. CMnd /\ ( M e. NN0 /\ X e. B /\ Y e. B ) ) -> ( M .x. ( X .+ Y ) ) = ( ( M .x. X ) .+ ( M .x. Y ) ) )

  proof
    cG
    ccmn
    wcel
    #
    cM
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
    #
    wa
    #
    cM
    cn
    wcel
    #
    cM
    cX
    cY
    c.pl
    co
    #
    c.x
    co
    #
    cM
    cX
    c.x
    co
    #
    cM
    cY
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    cM
    cc0
    wceq
    #
    @5
    @6
    wa
    #
    cM
    c.pl
    cn
    @7
    csn
    cxp
    #
    c1
    cseq
    #
    cfv
    #
    cM
    c.pl
    cn
    cX
    csn
    cxp
    #
    c1
    cseq
    #
    cfv
    #
    cM
    c.pl
    cn
    cY
    csn
    cxp
    #
    c1
    cseq
    #
    cfv
    #
    c.pl
    co
    @8
    @11
    @13
    vx
    vy
    vz
    c.pl
    cB
    vk
    @17
    @20
    @14
    c1
    cM
    @13
    cG
    cmnd
    wcel
    #
    vx
    cv
    #
    cB
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    #
    @24
    @26
    c.pl
    co
    #
    cB
    wcel
    #
    @0
    @23
    @4
    @6
    cG
    cmnmnd
    #
    ad2antrr
    #
    @23
    @25
    @27
    @30
    cB
    c.pl
    cG
    @24
    @26
    mulgdi.b
    mulgdi.p
    mndcl
    3expb
    sylan
    @13
    @0
    @28
    @29
    @26
    @24
    c.pl
    co
    wceq
    #
    @0
    @4
    @6
    simpll
    @0
    @25
    @27
    @33
    cB
    c.pl
    cG
    @24
    @26
    mulgdi.b
    mulgdi.p
    cmncom
    3expb
    sylan
    @13
    @23
    @25
    @27
    vz
    cv
    #
    cB
    wcel
    w3a
    @29
    @34
    c.pl
    co
    @24
    @26
    @34
    c.pl
    co
    c.pl
    co
    wceq
    @32
    cB
    c.pl
    cG
    @24
    @26
    @34
    mulgdi.b
    mulgdi.p
    mndass
    sylan
    @13
    cM
    cn
    c1
    cuz
    cfv
    @5
    @6
    simpr
    #
    nnuz
    syl6eleq
    @13
    vk
    cv
    #
    c1
    cM
    cfz
    co
    wcel
    #
    wa
    #
    @36
    @17
    cfv
    #
    cX
    cB
    @13
    @2
    @36
    cn
    wcel
    #
    @39
    cX
    wceq
    @37
    @1
    @2
    @3
    @0
    @6
    simplr2
    #
    @36
    cM
    elfznn
    #
    cn
    cX
    @36
    cB
    fvconst2g
    syl2an
    #
    @13
    @2
    @37
    @41
    adantr
    eqeltrd
    @38
    @36
    @20
    cfv
    #
    cY
    cB
    @13
    @3
    @40
    @44
    cY
    wceq
    @37
    @1
    @2
    @3
    @0
    @6
    simplr3
    #
    @42
    cn
    cY
    @36
    cB
    fvconst2g
    syl2an
    #
    @13
    @3
    @37
    @45
    adantr
    eqeltrd
    @38
    @36
    @14
    cfv
    #
    @7
    @39
    @44
    c.pl
    co
    @13
    @7
    cB
    wcel
    #
    @40
    @47
    @7
    wceq
    @37
    @13
    @23
    @2
    @3
    @48
    @32
    @41
    @45
    cB
    c.pl
    cG
    cX
    cY
    mulgdi.b
    mulgdi.p
    mndcl
    #
    syl3anc
    #
    @42
    cn
    @7
    @36
    cB
    fvconst2g
    syl2an
    @38
    @39
    cX
    @44
    cY
    c.pl
    @43
    @46
    oveq12d
    eqtr4d
    seqcaopr
    @13
    @6
    @48
    @8
    @16
    wceq
    @35
    @50
    cB
    c.pl
    @15
    c.x
    cG
    cM
    @7
    mulgdi.b
    mulgdi.p
    mulgdi.m
    @15
    eqid
    mulgnn
    syl2anc
    @13
    @9
    @19
    @10
    @22
    c.pl
    @13
    @6
    @2
    @9
    @19
    wceq
    @35
    @41
    cB
    c.pl
    @18
    c.x
    cG
    cM
    cX
    mulgdi.b
    mulgdi.p
    mulgdi.m
    @18
    eqid
    mulgnn
    syl2anc
    @13
    @6
    @3
    @10
    @22
    wceq
    @35
    @45
    cB
    c.pl
    @21
    c.x
    cG
    cM
    cY
    mulgdi.b
    mulgdi.p
    mulgdi.m
    @21
    eqid
    mulgnn
    syl2anc
    oveq12d
    3eqtr4d
    @5
    @12
    wa
    #
    cc0
    @7
    c.x
    co
    #
    cG
    c0g
    cfv
    #
    @53
    c.pl
    co
    #
    @8
    @11
    @51
    @52
    @53
    @54
    @51
    @48
    @52
    @53
    wceq
    @51
    @23
    @2
    @3
    @48
    @0
    @23
    @4
    @12
    @31
    ad2antrr
    @1
    @2
    @3
    @0
    @12
    simplr2
    #
    @1
    @2
    @3
    @0
    @12
    simplr3
    #
    @49
    syl3anc
    cB
    c.x
    cG
    @7
    @53
    mulgdi.b
    @53
    eqid
    #
    mulgdi.m
    mulg0
    syl
    @0
    @54
    @53
    wceq
    #
    @4
    @12
    @0
    @23
    @58
    @31
    @23
    @53
    cG
    cbs
    cfv
    #
    wcel
    @58
    @59
    cG
    @53
    @59
    eqid
    #
    @57
    mndidcl
    @59
    c.pl
    cG
    @53
    @53
    @60
    mulgdi.p
    @57
    mndlid
    mpdan
    syl
    ad2antrr
    eqtr4d
    @51
    cM
    cc0
    @7
    c.x
    @5
    @12
    simpr
    #
    oveq1d
    @51
    @9
    @53
    @10
    @53
    c.pl
    @51
    @9
    cc0
    cX
    c.x
    co
    #
    @53
    @51
    cM
    cc0
    cX
    c.x
    @61
    oveq1d
    @51
    @2
    @62
    @53
    wceq
    @55
    cB
    c.x
    cG
    cX
    @53
    mulgdi.b
    @57
    mulgdi.m
    mulg0
    syl
    eqtrd
    @51
    @10
    cc0
    cY
    c.x
    co
    #
    @53
    @51
    cM
    cc0
    cY
    c.x
    @61
    oveq1d
    @51
    @3
    @63
    @53
    wceq
    @56
    cB
    c.x
    cG
    cY
    @53
    mulgdi.b
    @57
    mulgdi.m
    mulg0
    syl
    eqtrd
    oveq12d
    3eqtr4d
    @5
    @1
    @6
    @12
    wo
    @0
    @1
    @2
    @3
    simpr1
    cM
    elnn0
    sylib
    mpjaodan
end
