include "cclm.mm"
include "wcel.mm"
include "cz.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "cc0.mm"
include "cneg.mm"
include "c1.mm"
include "caddc.mm"
include "wa.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "c0g.mm"
include "cfv.mm"
include "eqid.mm"
include "mulg0.mm"
include "adantl.mm"
include "csca.mm"
include "clm0vs.mm"
include "eqtr4d.mm"
include "cn0.mm"
include "wi.mm"
include "cplusg.mm"
include "cmnd.mm"
include "cgrp.mm"
include "clmgrp.mm"
include "grpmnd.mm"
include "syl.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "simplr.mm"
include "mulgnn0p1.mm"
include "syl3anc.mm"
include "cbs.mm"
include "simpll.mm"
include "wss.mm"
include "clmzss.mm"
include "nn0z.mm"
include "sseldd.mm"
include "1zzd.mm"
include "clmvsdir.mm"
include "syl13anc.mm"
include "clmvs1.mm"
include "adantr.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "syl5ibr.mm"
include "ex.mm"
include "cn.mm"
include "cminusg.mm"
include "fveq2.mm"
include "nnz.mm"
include "mulgneg.mm"
include "clmvsneg.mm"
include "eqcomd.mm"
include "zindd.mm"
include "3impia.mm"
include "3com23.mm"

theorem clmmulg
  let cA: class A
  let cB: class B
  let c.xb: class .xb
  let c.x: class .x.
  let cV: class V
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume clmmulg.1: |- V = ( Base ` W )
  assume clmmulg.2: |- .xb = ( .g ` W )
  assume clmmulg.3: |- .x. = ( .s ` W )


  assert |- ( ( W e. CMod /\ A e. ZZ /\ B e. V ) -> ( A .xb B ) = ( A .x. B ) )

  proof
    cW
    cclm
    wcel
    #
    cB
    cV
    wcel
    #
    cA
    cz
    wcel
    #
    cA
    cB
    c.xb
    co
    #
    cA
    cB
    c.x
    co
    #
    wceq
    #
    @0
    @1
    @2
    @5
    vx
    cv
    #
    cB
    c.xb
    co
    #
    @6
    cB
    c.x
    co
    #
    wceq
    cc0
    cB
    c.xb
    co
    #
    cc0
    cB
    c.x
    co
    #
    wceq
    vy
    cv
    #
    cB
    c.xb
    co
    #
    @11
    cB
    c.x
    co
    #
    wceq
    #
    @11
    cneg
    #
    cB
    c.xb
    co
    #
    @15
    cB
    c.x
    co
    #
    wceq
    #
    @11
    c1
    caddc
    co
    #
    cB
    c.xb
    co
    #
    @19
    cB
    c.x
    co
    #
    wceq
    #
    @5
    @0
    @1
    wa
    #
    vx
    vy
    cA
    @6
    cc0
    wceq
    @7
    @9
    @8
    @10
    @6
    cc0
    cB
    c.xb
    oveq1
    @6
    cc0
    cB
    c.x
    oveq1
    eqeq12d
    @6
    @11
    wceq
    @7
    @12
    @8
    @13
    @6
    @11
    cB
    c.xb
    oveq1
    @6
    @11
    cB
    c.x
    oveq1
    eqeq12d
    @6
    @19
    wceq
    @7
    @20
    @8
    @21
    @6
    @19
    cB
    c.xb
    oveq1
    @6
    @19
    cB
    c.x
    oveq1
    eqeq12d
    @6
    @15
    wceq
    @7
    @16
    @8
    @17
    @6
    @15
    cB
    c.xb
    oveq1
    @6
    @15
    cB
    c.x
    oveq1
    eqeq12d
    @6
    cA
    wceq
    @7
    @3
    @8
    @4
    @6
    cA
    cB
    c.xb
    oveq1
    @6
    cA
    cB
    c.x
    oveq1
    eqeq12d
    @23
    @9
    cW
    c0g
    cfv
    #
    @10
    @1
    @9
    @24
    wceq
    @0
    cV
    c.xb
    cW
    cB
    @24
    clmmulg.1
    @24
    eqid
    #
    clmmulg.2
    mulg0
    adantl
    c.x
    cW
    csca
    cfv
    #
    cV
    cW
    cB
    @24
    clmmulg.1
    @26
    eqid
    #
    clmmulg.3
    @25
    clm0vs
    eqtr4d
    @23
    @11
    cn0
    wcel
    #
    @14
    @22
    wi
    @14
    @22
    @23
    @28
    wa
    #
    @12
    cB
    cW
    cplusg
    cfv
    #
    co
    #
    @13
    cB
    @30
    co
    #
    wceq
    @12
    @13
    cB
    @30
    oveq1
    @29
    @20
    @31
    @21
    @32
    @29
    cW
    cmnd
    wcel
    #
    @28
    @1
    @20
    @31
    wceq
    @0
    @33
    @1
    @28
    @0
    cW
    cgrp
    wcel
    #
    @33
    cW
    clmgrp
    #
    cW
    grpmnd
    syl
    ad2antrr
    @23
    @28
    simpr
    @0
    @1
    @28
    simplr
    #
    cV
    @30
    c.xb
    cW
    @11
    cB
    clmmulg.1
    clmmulg.2
    @30
    eqid
    #
    mulgnn0p1
    syl3anc
    @29
    @21
    @13
    c1
    cB
    c.x
    co
    #
    @30
    co
    #
    @32
    @29
    @0
    @11
    @26
    cbs
    cfv
    #
    wcel
    c1
    @40
    wcel
    @1
    @21
    @39
    wceq
    @0
    @1
    @28
    simpll
    @29
    cz
    @40
    @11
    @0
    cz
    @40
    wss
    #
    @1
    @28
    @26
    @40
    cW
    @27
    @40
    eqid
    #
    clmzss
    #
    ad2antrr
    #
    @28
    @11
    cz
    wcel
    #
    @23
    @11
    nn0z
    adantl
    sseldd
    @29
    cz
    @40
    c1
    @44
    @29
    1zzd
    sseldd
    @36
    @30
    @11
    c1
    c.x
    @26
    @40
    cV
    cW
    cB
    clmmulg.1
    @27
    clmmulg.3
    @42
    @37
    clmvsdir
    syl13anc
    @29
    @38
    cB
    @13
    @30
    @23
    @38
    cB
    wceq
    @28
    c.x
    cV
    cW
    cB
    clmmulg.1
    clmmulg.3
    clmvs1
    adantr
    oveq2d
    eqtrd
    eqeq12d
    syl5ibr
    ex
    @23
    @11
    cn
    wcel
    #
    @14
    @18
    wi
    @14
    @18
    @23
    @46
    wa
    #
    @12
    cW
    cminusg
    cfv
    #
    cfv
    #
    @13
    @48
    cfv
    #
    wceq
    @12
    @13
    @48
    fveq2
    @47
    @16
    @49
    @17
    @50
    @47
    @34
    @45
    @1
    @16
    @49
    wceq
    @0
    @34
    @1
    @46
    @35
    ad2antrr
    @46
    @45
    @23
    @11
    nnz
    adantl
    #
    @0
    @1
    @46
    simplr
    #
    cV
    c.xb
    cW
    @48
    @11
    cB
    clmmulg.1
    clmmulg.2
    @48
    eqid
    #
    mulgneg
    syl3anc
    @47
    @50
    @17
    @47
    cV
    @11
    c.x
    @26
    @40
    @48
    cW
    cB
    clmmulg.1
    @27
    clmmulg.3
    @53
    @42
    @0
    @1
    @46
    simpll
    @52
    @47
    cz
    @40
    @11
    @0
    @41
    @1
    @46
    @43
    ad2antrr
    @51
    sseldd
    clmvsneg
    eqcomd
    eqeq12d
    syl5ibr
    ex
    zindd
    3impia
    3com23
end
