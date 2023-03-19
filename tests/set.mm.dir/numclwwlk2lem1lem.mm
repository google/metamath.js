include "cwwlksn.mm"
include "co.mm"
include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "clsw.mm"
include "cc0.mm"
include "wne.mm"
include "cs1.mm"
include "cconcat.mm"
include "wceq.mm"
include "wa.mm"
include "cn0.mm"
include "cword.mm"
include "chash.mm"
include "c1.mm"
include "caddc.mm"
include "w3a.mm"
include "wi.mm"
include "wwlknbp1.mm"
include "clt.mm"
include "wbr.mm"
include "simpl2.mm"
include "s1cl.mm"
include "ad2antrl.mm"
include "nn0p1gt0.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "wb.mm"
include "breq2.mm"
include "3ad2ant3.mm"
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
include "adantl.mm"
include "hashneq0.mm"
include "bicomd.mm"
include "3ad2ant2.mm"
include "ccatval1lsw.mm"
include "neeq1d.mm"
include "biimpd.mm"
include "impr.mm"
include "jca.mm"
include "exp32.mm"
include "3imp21.mm"

theorem numclwwlk2lem1lem
  let cG: class G
  let cN: class N
  let cW: class W
  let cX: class X
  let vi: setvar i


  assert |- ( ( X e. ( Vtx ` G ) /\ W e. ( N WWalksN G ) /\ ( lastS ` W ) =/= ( W ` 0 ) ) -> ( ( ( W ++ <" X "> ) ` 0 ) = ( W ` 0 ) /\ ( ( W ++ <" X "> ) ` N ) =/= ( W ` 0 ) ) )

  proof
    cW
    cN
    cG
    cwwlksn
    co
    wcel
    #
    cX
    cG
    cvtx
    cfv
    #
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
    cc0
    cW
    cX
    cs1
    #
    cconcat
    co
    #
    cfv
    @4
    wceq
    #
    cN
    @7
    cfv
    #
    @4
    wne
    #
    wa
    #
    @0
    cN
    cn0
    wcel
    #
    cW
    @1
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
    w3a
    #
    @2
    @5
    @11
    wi
    wi
    cG
    cN
    cW
    wwlknbp1
    @18
    @2
    @5
    @11
    @18
    @2
    @5
    wa
    #
    wa
    #
    @8
    @10
    @20
    @14
    @6
    @13
    wcel
    #
    cc0
    @15
    clt
    wbr
    #
    @8
    @12
    @14
    @17
    @19
    simpl2
    @2
    @21
    @18
    @5
    cX
    @1
    s1cl
    #
    ad2antrl
    @20
    @22
    cc0
    @16
    clt
    wbr
    #
    @18
    @24
    @19
    @12
    @14
    @24
    @17
    cN
    nn0p1gt0
    3ad2ant1
    #
    adantr
    @18
    @22
    @24
    wb
    #
    @19
    @17
    @12
    @26
    @14
    @15
    @16
    cc0
    clt
    breq2
    3ad2ant3
    #
    adantr
    mpbird
    cW
    @6
    @1
    ccatfv0
    syl3anc
    @18
    @2
    @5
    @10
    @18
    @2
    wa
    #
    @5
    @10
    @28
    @3
    @9
    @4
    @28
    @9
    @15
    c1
    cmin
    co
    #
    @7
    cfv
    #
    @3
    @28
    cN
    @29
    @7
    @18
    cN
    @29
    wceq
    @2
    @18
    @29
    @16
    c1
    cmin
    co
    #
    cN
    @17
    @12
    @29
    @31
    wceq
    @14
    @15
    @16
    c1
    cmin
    oveq1
    3ad2ant3
    @12
    @14
    @31
    cN
    wceq
    #
    @17
    @12
    cN
    cc
    wcel
    @32
    cN
    nn0cn
    cN
    pncan1
    syl
    3ad2ant1
    eqtr2d
    adantr
    fveq2d
    @28
    @14
    @21
    cW
    c0
    wne
    #
    @30
    @3
    wceq
    @12
    @14
    @17
    @2
    simpl2
    @2
    @21
    @18
    @23
    adantl
    @28
    @33
    @22
    @28
    @22
    @24
    @18
    @24
    @2
    @25
    adantr
    @18
    @26
    @2
    @27
    adantr
    mpbird
    @18
    @33
    @22
    wb
    #
    @2
    @14
    @12
    @34
    @17
    @14
    @22
    @33
    cW
    @13
    hashneq0
    bicomd
    3ad2ant2
    adantr
    mpbird
    cW
    @6
    @1
    ccatval1lsw
    syl3anc
    eqtr2d
    neeq1d
    biimpd
    impr
    jca
    exp32
    syl
    3imp21
end
