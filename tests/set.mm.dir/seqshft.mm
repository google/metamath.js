include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cuz.mm"
include "cfv.mm"
include "cshi.mm"
include "co.mm"
include "cseq.mm"
include "cmin.mm"
include "wfn.mm"
include "seqfn.mm"
include "adantr.mm"
include "cv.mm"
include "cc.mm"
include "crab.mm"
include "zsubcl.mm"
include "syl.mm"
include "zcn.mm"
include "adantl.mm"
include "seqex.mm"
include "shftfn.mm"
include "syl2anc.mm"
include "caddc.mm"
include "wceq.mm"
include "simpr.mm"
include "shftuz.mm"
include "npcan.mm"
include "syl2an.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "fneq2d.mm"
include "mpbid.mm"
include "cneg.mm"
include "negsub.mm"
include "seqeq1d.mm"
include "eluzelcn.mm"
include "syl2anr.mm"
include "fveq12d.mm"
include "znegcl.mm"
include "ad2antlr.mm"
include "cfz.mm"
include "elfzelz.mm"
include "zcnd.mm"
include "shftval.mm"
include "ancoms.mm"
include "eqtr4d.mm"
include "ad4ant24.mm"
include "seqshft2.mm"
include "3eqtr4d.mm"
include "eqfnfvd.mm"

theorem seqshft
  let c.pl: class .+
  let cF: class F
  let cM: class M
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume seqshft.1: |- F e. _V


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> seq M ( .+ , ( F shift N ) ) = ( seq ( M - N ) ( .+ , F ) shift N ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    vz
    cM
    cuz
    cfv
    #
    c.pl
    cF
    cN
    cshi
    co
    #
    cM
    cseq
    #
    c.pl
    cF
    cM
    cN
    cmin
    co
    #
    cseq
    #
    cN
    cshi
    co
    #
    @0
    @5
    @3
    wfn
    @1
    c.pl
    @4
    cM
    seqfn
    adantr
    @2
    @8
    vx
    cv
    cN
    cmin
    co
    @6
    cuz
    cfv
    #
    wcel
    vx
    cc
    crab
    #
    wfn
    #
    @8
    @3
    wfn
    @2
    @7
    @9
    wfn
    #
    cN
    cc
    wcel
    #
    @11
    @2
    @6
    cz
    wcel
    #
    @12
    cM
    cN
    zsubcl
    #
    c.pl
    cF
    @6
    seqfn
    syl
    @1
    @13
    @0
    cN
    zcn
    #
    adantl
    #
    vx
    cN
    @9
    @7
    c.pl
    cF
    @6
    seqex
    #
    shftfn
    syl2anc
    @2
    @10
    @3
    @8
    @2
    @10
    @6
    cN
    caddc
    co
    #
    cuz
    cfv
    #
    @3
    @2
    @1
    @14
    @10
    @20
    wceq
    @0
    @1
    simpr
    @15
    vx
    cN
    @6
    shftuz
    syl2anc
    @2
    @19
    cM
    cuz
    @0
    cM
    cc
    wcel
    #
    @13
    @19
    cM
    wceq
    @1
    cM
    zcn
    #
    @16
    cM
    cN
    npcan
    syl2an
    fveq2d
    eqtrd
    fneq2d
    mpbid
    @2
    vz
    cv
    #
    @3
    wcel
    #
    wa
    #
    @23
    cN
    cneg
    #
    caddc
    co
    #
    c.pl
    cF
    cM
    @26
    caddc
    co
    #
    cseq
    #
    cfv
    @23
    cN
    cmin
    co
    #
    @7
    cfv
    #
    @23
    @5
    cfv
    @23
    @8
    cfv
    #
    @25
    @27
    @30
    @29
    @7
    @25
    @28
    @6
    c.pl
    cF
    @2
    @28
    @6
    wceq
    #
    @24
    @0
    @21
    @13
    @33
    @1
    @22
    @16
    cM
    cN
    negsub
    syl2an
    adantr
    seqeq1d
    @24
    @23
    cc
    wcel
    #
    @13
    @27
    @30
    wceq
    @2
    cM
    @23
    eluzelcn
    #
    @17
    @23
    cN
    negsub
    syl2anr
    fveq12d
    @25
    c.pl
    vy
    @4
    cF
    @26
    cM
    @23
    @2
    @24
    simpr
    @1
    @26
    cz
    wcel
    @0
    @24
    cN
    znegcl
    ad2antlr
    @1
    vy
    cv
    #
    cM
    @23
    cfz
    co
    wcel
    #
    @36
    @4
    cfv
    #
    @36
    @26
    caddc
    co
    #
    cF
    cfv
    #
    wceq
    #
    @0
    @24
    @1
    @13
    @36
    cc
    wcel
    #
    @41
    @37
    @16
    @37
    @36
    @36
    cM
    @23
    elfzelz
    zcnd
    @13
    @42
    wa
    #
    @38
    @36
    cN
    cmin
    co
    #
    cF
    cfv
    @40
    cN
    @36
    cF
    seqshft.1
    shftval
    @43
    @39
    @44
    cF
    @42
    @13
    @39
    @44
    wceq
    @36
    cN
    negsub
    ancoms
    fveq2d
    eqtr4d
    syl2an
    ad4ant24
    seqshft2
    @2
    @13
    @34
    @32
    @31
    wceq
    @24
    @17
    @35
    cN
    @23
    @7
    @18
    shftval
    syl2an
    3eqtr4d
    eqfnfvd
end
