include "cq.mm"
include "wcel.mm"
include "cdenom.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cz.mm"
include "wa.mm"
include "cnumer.mm"
include "cdiv.mm"
include "co.mm"
include "qeqnumdivden.mm"
include "adantr.mm"
include "oveq2.mm"
include "adantl.mm"
include "qnumcl.mm"
include "zcnd.mm"
include "div1d.mm"
include "3eqtrd.mm"
include "eqeltrd.mm"
include "cle.mm"
include "wbr.mm"
include "simpr.mm"
include "fveq2d.mm"
include "cn.mm"
include "1nn.mm"
include "divdenle.mm"
include "sylancl.mm"
include "eqbrtrrd.mm"
include "wb.mm"
include "qdencl.mm"
include "nnle1eq1.mm"
include "syl.mm"
include "mpbid.mm"
include "impbida.mm"

theorem qden1elz
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( A e. QQ -> ( ( denom ` A ) = 1 <-> A e. ZZ ) )

  proof
    cA
    cq
    wcel
    #
    cA
    cdenom
    cfv
    #
    c1
    wceq
    #
    cA
    cz
    wcel
    #
    @0
    @2
    wa
    #
    cA
    cA
    cnumer
    cfv
    #
    cz
    @4
    cA
    @5
    @1
    cdiv
    co
    #
    @5
    c1
    cdiv
    co
    #
    @5
    @0
    cA
    @6
    wceq
    @2
    cA
    qeqnumdivden
    adantr
    @2
    @6
    @7
    wceq
    @0
    @1
    c1
    @5
    cdiv
    oveq2
    adantl
    @4
    @5
    @4
    @5
    @0
    @5
    cz
    wcel
    @2
    cA
    qnumcl
    adantr
    #
    zcnd
    div1d
    3eqtrd
    @8
    eqeltrd
    @0
    @3
    wa
    #
    @1
    c1
    cle
    wbr
    #
    @2
    @9
    cA
    c1
    cdiv
    co
    #
    cdenom
    cfv
    #
    @1
    c1
    cle
    @9
    @11
    cA
    cdenom
    @9
    cA
    @9
    cA
    @0
    @3
    simpr
    #
    zcnd
    div1d
    fveq2d
    @9
    @3
    c1
    cn
    wcel
    @12
    c1
    cle
    wbr
    @13
    1nn
    cA
    c1
    divdenle
    sylancl
    eqbrtrrd
    @9
    @1
    cn
    wcel
    #
    @10
    @2
    wb
    @0
    @14
    @3
    cA
    qdencl
    adantr
    @1
    nnle1eq1
    syl
    mpbid
    impbida
end
