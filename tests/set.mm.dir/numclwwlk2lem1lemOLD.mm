include "cwwlksn.mm"
include "co.mm"
include "wcel.mm"
include "clsw.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cn0.mm"
include "cvtx.mm"
include "cs1.mm"
include "cconcat.mm"
include "wceq.mm"
include "wi.mm"
include "cword.mm"
include "chash.mm"
include "c1.mm"
include "caddc.mm"
include "wwlknbp2OLD.mm"
include "clt.mm"
include "wbr.mm"
include "simpll.mm"
include "s1cl.mm"
include "adantl.mm"
include "nn0p1gt0.mm"
include "adantr.mm"
include "wb.mm"
include "breq2.mm"
include "mpbird.mm"
include "ccatfv0.mm"
include "syl3anc.mm"
include "cmin.mm"
include "oveq1.mm"
include "cc.mm"
include "nn0cn.mm"
include "pncan1.mm"
include "syl.mm"
include "eqtr2d.mm"
include "fveq2d.mm"
include "c0.mm"
include "hashneq0.mm"
include "bicomd.mm"
include "ccatval1lsw.mm"
include "neeq1d.mm"
include "biimpd.mm"
include "ex.mm"
include "com23.mm"
include "imp32.mm"
include "jca.mm"
include "exp32.mm"
include "imp.mm"
include "impcom.mm"

theorem numclwwlk2lem1lemOLD
  let cG: class G
  let cN: class N
  let cW: class W
  let cX: class X
  let vi: setvar i


  assert |- ( ( ( N e. NN0 /\ X e. ( Vtx ` G ) ) /\ ( W e. ( N WWalksN G ) /\ ( lastS ` W ) =/= ( W ` 0 ) ) ) -> ( ( ( W ++ <" X "> ) ` 0 ) = ( W ` 0 ) /\ ( ( W ++ <" X "> ) ` N ) =/= ( W ` 0 ) ) )

  proof
    cW
    cN
    cG
    cwwlksn
    co
    wcel
    #
    cW
    clsw
    cfv
    #
    cc0
    cW
    cfv
    #
    wne
    #
    wa
    cN
    cn0
    wcel
    #
    cX
    cG
    cvtx
    cfv
    #
    wcel
    #
    wa
    #
    cc0
    cW
    cX
    cs1
    #
    cconcat
    co
    #
    cfv
    @2
    wceq
    #
    cN
    @9
    cfv
    #
    @2
    wne
    #
    wa
    #
    @0
    @3
    @7
    @13
    wi
    #
    @0
    cW
    @5
    cword
    #
    wcel
    #
    cW
    chash
    cfv
    #
    cN
    c1
    caddc
    co
    #
    wceq
    #
    wa
    #
    @3
    @14
    wi
    cG
    cN
    cW
    wwlknbp2OLD
    @20
    @3
    @7
    @13
    @20
    @3
    @7
    wa
    #
    wa
    #
    @10
    @12
    @22
    @16
    @8
    @15
    wcel
    #
    cc0
    @17
    clt
    wbr
    #
    @10
    @16
    @19
    @21
    simpll
    @21
    @23
    @20
    @7
    @23
    @3
    @6
    @23
    @4
    cX
    @5
    s1cl
    adantl
    #
    adantl
    adantl
    @22
    @24
    cc0
    @18
    clt
    wbr
    #
    @21
    @26
    @20
    @7
    @26
    @3
    @4
    @26
    @6
    cN
    nn0p1gt0
    adantr
    #
    adantl
    adantl
    @20
    @24
    @26
    wb
    #
    @21
    @19
    @28
    @16
    @17
    @18
    cc0
    clt
    breq2
    adantl
    #
    adantr
    mpbird
    cW
    @8
    @5
    ccatfv0
    syl3anc
    @20
    @3
    @7
    @12
    @20
    @7
    @3
    @12
    @20
    @7
    @3
    @12
    wi
    @20
    @7
    wa
    #
    @3
    @12
    @30
    @1
    @11
    @2
    @30
    @11
    @17
    c1
    cmin
    co
    #
    @9
    cfv
    #
    @1
    @30
    cN
    @31
    @9
    @30
    @31
    @18
    c1
    cmin
    co
    #
    cN
    @20
    @31
    @33
    wceq
    #
    @7
    @19
    @34
    @16
    @17
    @18
    c1
    cmin
    oveq1
    adantl
    adantr
    @7
    @33
    cN
    wceq
    #
    @20
    @4
    @35
    @6
    @4
    cN
    cc
    wcel
    @35
    cN
    nn0cn
    cN
    pncan1
    syl
    adantr
    adantl
    eqtr2d
    fveq2d
    @30
    @16
    @23
    cW
    c0
    wne
    #
    @32
    @1
    wceq
    @16
    @19
    @7
    simpll
    @7
    @23
    @20
    @25
    adantl
    @30
    @36
    @24
    @30
    @24
    @26
    @7
    @26
    @20
    @27
    adantl
    @20
    @28
    @7
    @29
    adantr
    mpbird
    @20
    @36
    @24
    wb
    #
    @7
    @16
    @37
    @19
    @16
    @24
    @36
    cW
    @15
    hashneq0
    bicomd
    adantr
    adantr
    mpbird
    cW
    @8
    @5
    ccatval1lsw
    syl3anc
    eqtr2d
    neeq1d
    biimpd
    ex
    com23
    imp32
    jca
    exp32
    syl
    imp
    impcom
end
