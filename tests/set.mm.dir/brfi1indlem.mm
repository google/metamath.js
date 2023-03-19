include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "csn.mm"
include "cdif.mm"
include "wa.mm"
include "cmin.mm"
include "cfn.mm"
include "wss.mm"
include "wi.mm"
include "peano2nn0.mm"
include "eleq1a.mm"
include "adantr.mm"
include "imp.mm"
include "wb.mm"
include "hashclb.mm"
include "ad2antlr.mm"
include "mpbird.mm"
include "ex.mm"
include "syl.mm"
include "impcom.mm"
include "3adant2.mm"
include "snssi.mm"
include "3ad2ant2.mm"
include "hashssdif.mm"
include "syl2anc.mm"
include "oveq1.mm"
include "hashsng.mm"
include "oveq2d.mm"
include "nn0cn.mm"
include "1cnd.mm"
include "pncand.mm"
include "3ad2ant3.mm"
include "eqtrd.mm"
include "sylan9eqr.mm"

theorem brfi1indlem
  let cN: class N
  let cV: class V
  let cW: class W
  let cY: class Y


  assert |- ( ( V e. W /\ N e. V /\ Y e. NN0 ) -> ( ( # ` V ) = ( Y + 1 ) -> ( # ` ( V \ { N } ) ) = Y ) )

  proof
    cV
    cW
    wcel
    #
    cN
    cV
    wcel
    #
    cY
    cn0
    wcel
    #
    w3a
    #
    cV
    chash
    cfv
    #
    cY
    c1
    caddc
    co
    #
    wceq
    #
    cV
    cN
    csn
    #
    cdif
    chash
    cfv
    #
    cY
    wceq
    @3
    @6
    wa
    #
    @8
    @4
    @7
    chash
    cfv
    #
    cmin
    co
    #
    cY
    @9
    cV
    cfn
    wcel
    #
    @7
    cV
    wss
    #
    @8
    @11
    wceq
    @3
    @6
    @12
    @0
    @2
    @6
    @12
    wi
    #
    @1
    @2
    @0
    @14
    @2
    @5
    cn0
    wcel
    #
    @0
    @14
    wi
    cY
    peano2nn0
    @15
    @0
    @14
    @15
    @0
    wa
    #
    @6
    @12
    @16
    @6
    wa
    @12
    @4
    cn0
    wcel
    #
    @16
    @6
    @17
    @15
    @6
    @17
    wi
    @0
    @5
    cn0
    @4
    eleq1a
    adantr
    imp
    @0
    @12
    @17
    wb
    @15
    @6
    cV
    cW
    hashclb
    ad2antlr
    mpbird
    ex
    ex
    syl
    impcom
    3adant2
    imp
    @3
    @13
    @6
    @1
    @0
    @13
    @2
    cN
    cV
    snssi
    3ad2ant2
    adantr
    cV
    @7
    hashssdif
    syl2anc
    @6
    @3
    @11
    @5
    @10
    cmin
    co
    #
    cY
    @4
    @5
    @10
    cmin
    oveq1
    @3
    @18
    @5
    c1
    cmin
    co
    #
    cY
    @1
    @0
    @18
    @19
    wceq
    @2
    @1
    @10
    c1
    @5
    cmin
    cN
    cV
    hashsng
    oveq2d
    3ad2ant2
    @2
    @0
    @19
    cY
    wceq
    @1
    @2
    cY
    c1
    cY
    nn0cn
    @2
    1cnd
    pncand
    3ad2ant3
    eqtrd
    sylan9eqr
    eqtrd
    ex
end
