include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "csgn.mm"
include "cfv.mm"
include "wceq.mm"
include "cc0.mm"
include "c1.mm"
include "cneg.mm"
include "remulcl.mm"
include "rexrd.mm"
include "eqeq1.mm"
include "fveq2.mm"
include "sgn0.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "adantl.mm"
include "sgnclre.mm"
include "recnd.mm"
include "mul02d.mm"
include "ad3antlr.mm"
include "eqtr2d.mm"
include "oveq2d.mm"
include "mul01d.mm"
include "ad3antrrr.mm"
include "wo.mm"
include "simpl.mm"
include "simpr.mm"
include "mul0ord.mm"
include "biimpa.mm"
include "mpjaodan.mm"
include "clt.mm"
include "wbr.mm"
include "simpll.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "wn.mm"
include "cc.mm"
include "adantr.mm"
include "gt0ne0d.mm"
include "mulne0bad.mm"
include "neneqd.mm"
include "pm2.21dd.mm"
include "cxr.mm"
include "ad2antrr.mm"
include "cle.mm"
include "0red.mm"
include "simplll.mm"
include "ltled.mm"
include "simplr.mm"
include "prodgt0.mm"
include "syl12anc.mm"
include "sgnp.mm"
include "syl2anc.mm"
include "1t1e1.mm"
include "syl6req.mm"
include "renegcld.mm"
include "wb.mm"
include "lt0neg1d.mm"
include "mpbid.mm"
include "mul2negd.mm"
include "breqtrrd.mm"
include "syl22anc.mm"
include "mpbird.mm"
include "sgnn.mm"
include "neg1mulneg1e1.mm"
include "sgn3da.mm"
include "lt0ne0d.mm"
include "mulcomd.mm"
include "breq1d.mm"
include "mul2lt0rgt0.mm"
include "neg1cn.mm"
include "mulid2i.mm"
include "mul2lt0rlt0.mm"
include "mulid1i.mm"

theorem sgnmul
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( sgn ` ( A x. B ) ) = ( ( sgn ` A ) x. ( sgn ` B ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cA
    cB
    cmul
    co
    #
    csgn
    cfv
    #
    cA
    csgn
    cfv
    #
    cB
    csgn
    cfv
    #
    cmul
    co
    #
    wceq
    cc0
    @7
    wceq
    #
    c1
    @7
    wceq
    #
    c1
    cneg
    #
    @7
    wceq
    #
    @3
    @2
    @3
    cA
    cB
    remulcl
    rexrd
    @4
    cc0
    @7
    eqeq1
    @4
    c1
    @7
    eqeq1
    @4
    @10
    @7
    eqeq1
    @2
    @3
    cc0
    wceq
    #
    wa
    #
    cA
    cc0
    wceq
    #
    @8
    cB
    cc0
    wceq
    #
    @13
    @14
    wa
    @7
    cc0
    @6
    cmul
    co
    #
    cc0
    @14
    @7
    @16
    wceq
    @13
    @14
    @5
    cc0
    @6
    cmul
    @14
    @5
    cc0
    csgn
    cfv
    #
    cc0
    cA
    cc0
    csgn
    fveq2
    sgn0
    syl6eq
    oveq1d
    adantl
    @1
    @16
    cc0
    wceq
    @0
    @12
    @14
    @1
    @6
    @1
    @6
    cB
    sgnclre
    recnd
    mul02d
    ad3antlr
    eqtr2d
    @13
    @15
    wa
    @7
    @5
    cc0
    cmul
    co
    #
    cc0
    @15
    @7
    @18
    wceq
    @13
    @15
    @6
    cc0
    @5
    cmul
    @15
    @6
    @17
    cc0
    cB
    cc0
    csgn
    fveq2
    sgn0
    syl6eq
    oveq2d
    adantl
    @0
    @18
    cc0
    wceq
    @1
    @12
    @15
    @0
    @5
    @0
    @5
    cA
    sgnclre
    recnd
    mul01d
    ad3antrrr
    eqtr2d
    @2
    @12
    @14
    @15
    wo
    @2
    cA
    cB
    @2
    cA
    @0
    @1
    simpl
    #
    recnd
    #
    @2
    cB
    @0
    @1
    simpr
    #
    recnd
    #
    mul0ord
    biimpa
    mpjaodan
    @2
    cc0
    @3
    clt
    wbr
    #
    wa
    #
    @9
    c1
    @16
    wceq
    #
    c1
    c1
    @6
    cmul
    co
    #
    wceq
    c1
    @10
    @6
    cmul
    co
    #
    wceq
    cA
    @24
    cA
    @0
    @1
    @23
    simpll
    rexrd
    @5
    cc0
    wceq
    #
    @7
    @16
    c1
    @5
    cc0
    @6
    cmul
    oveq1
    #
    eqeq2d
    @5
    c1
    wceq
    #
    @7
    @26
    c1
    @5
    c1
    @6
    cmul
    oveq1
    #
    eqeq2d
    @5
    @10
    wceq
    #
    @7
    @27
    c1
    @5
    @10
    @6
    cmul
    oveq1
    #
    eqeq2d
    @24
    @14
    wa
    @14
    @25
    @24
    @14
    simpr
    @24
    @14
    wn
    @14
    @24
    cA
    cc0
    @24
    cA
    cB
    @2
    cA
    cc
    wcel
    #
    @23
    @20
    adantr
    @2
    cB
    cc
    wcel
    #
    @23
    @22
    adantr
    @24
    @3
    @2
    @23
    simpr
    gt0ne0d
    mulne0bad
    neneqd
    adantr
    pm2.21dd
    @24
    cc0
    cA
    clt
    wbr
    #
    wa
    #
    @26
    c1
    c1
    cmul
    co
    c1
    @37
    @6
    c1
    c1
    cmul
    @37
    cB
    cxr
    wcel
    #
    cc0
    cB
    clt
    wbr
    #
    @6
    c1
    wceq
    #
    @37
    cB
    @2
    @1
    @23
    @36
    @21
    ad2antrr
    rexrd
    @37
    @2
    cc0
    cA
    cle
    wbr
    @23
    @39
    @2
    @23
    @36
    simpll
    @37
    cc0
    cA
    @37
    0red
    @0
    @1
    @23
    @36
    simplll
    @24
    @36
    simpr
    ltled
    @2
    @23
    @36
    simplr
    cA
    cB
    prodgt0
    syl12anc
    cB
    sgnp
    #
    syl2anc
    oveq2d
    1t1e1
    syl6req
    @24
    cA
    cc0
    clt
    wbr
    #
    wa
    #
    @27
    @10
    @10
    cmul
    co
    c1
    @43
    @6
    @10
    @10
    cmul
    @43
    @38
    cB
    cc0
    clt
    wbr
    #
    @6
    @10
    wceq
    #
    @43
    cB
    @2
    @1
    @23
    @42
    @21
    ad2antrr
    #
    rexrd
    @43
    @44
    cc0
    cB
    cneg
    #
    clt
    wbr
    #
    @43
    cA
    cneg
    #
    cr
    wcel
    @47
    cr
    wcel
    cc0
    @49
    cle
    wbr
    cc0
    @49
    @47
    cmul
    co
    #
    clt
    wbr
    @48
    @43
    cA
    @0
    @1
    @23
    @42
    simplll
    renegcld
    #
    @43
    cB
    @46
    renegcld
    @43
    cc0
    @49
    @43
    0red
    @51
    @43
    @42
    cc0
    @49
    clt
    wbr
    #
    @24
    @42
    simpr
    @2
    @42
    @52
    wb
    @23
    @42
    @2
    cA
    @19
    lt0neg1d
    ad2antrr
    mpbid
    ltled
    @43
    cc0
    @3
    @50
    clt
    @2
    @23
    @42
    simplr
    @43
    cA
    cB
    @2
    @34
    @23
    @42
    @20
    ad2antrr
    @2
    @35
    @23
    @42
    @22
    ad2antrr
    mul2negd
    breqtrrd
    @49
    @47
    prodgt0
    syl22anc
    @2
    @44
    @48
    wb
    @23
    @42
    @2
    cB
    @21
    lt0neg1d
    ad2antrr
    mpbird
    cB
    sgnn
    #
    syl2anc
    oveq2d
    neg1mulneg1e1
    syl6req
    sgn3da
    @2
    @3
    cc0
    clt
    wbr
    #
    wa
    #
    @11
    @10
    @16
    wceq
    #
    @10
    @26
    wceq
    @10
    @27
    wceq
    cA
    @55
    cA
    @0
    @1
    @54
    simpll
    #
    rexrd
    @28
    @7
    @16
    @10
    @29
    eqeq2d
    @30
    @7
    @26
    @10
    @31
    eqeq2d
    @32
    @7
    @27
    @10
    @33
    eqeq2d
    @55
    @14
    wa
    #
    @14
    @56
    @55
    @14
    simpr
    @58
    cA
    cc0
    @58
    cA
    cB
    @2
    @34
    @54
    @14
    @20
    ad2antrr
    @2
    @35
    @54
    @14
    @22
    ad2antrr
    @58
    @3
    @2
    @54
    @14
    simplr
    lt0ne0d
    mulne0bad
    neneqd
    pm2.21dd
    @55
    @36
    wa
    #
    @26
    c1
    @10
    cmul
    co
    @10
    @59
    @6
    @10
    c1
    cmul
    @59
    @38
    @44
    @45
    @59
    cB
    @2
    @1
    @54
    @36
    @21
    ad2antrr
    rexrd
    @55
    cB
    cA
    @0
    @1
    @54
    simplr
    #
    @57
    @2
    @54
    cB
    cA
    cmul
    co
    #
    cc0
    clt
    wbr
    @2
    @3
    @61
    cc0
    clt
    @2
    cA
    cB
    @20
    @22
    mulcomd
    breq1d
    biimpa
    #
    mul2lt0rgt0
    @53
    syl2anc
    oveq2d
    @10
    neg1cn
    mulid2i
    syl6req
    @55
    @42
    wa
    #
    @27
    @10
    c1
    cmul
    co
    @10
    @63
    @6
    c1
    @10
    cmul
    @63
    @38
    @39
    @40
    @63
    cB
    @55
    @1
    @42
    @60
    adantr
    rexrd
    @55
    cB
    cA
    @60
    @57
    @62
    mul2lt0rlt0
    @41
    syl2anc
    oveq2d
    @10
    neg1cn
    mulid1i
    syl6req
    sgn3da
    sgn3da
end
