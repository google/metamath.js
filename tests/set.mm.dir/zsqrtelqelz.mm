include "cz.mm"
include "wcel.mm"
include "csqrt.mm"
include "cfv.mm"
include "cq.mm"
include "wa.mm"
include "cdenom.mm"
include "c1.mm"
include "wceq.mm"
include "cn.mm"
include "qdencl.mm"
include "adantl.mm"
include "nnred.mm"
include "1red.mm"
include "nnnn0d.mm"
include "nn0ge0d.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "0le1.mm"
include "a1i.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "sq1.mm"
include "zcn.mm"
include "sqsqrtd.mm"
include "adantr.mm"
include "fveq2d.mm"
include "simpl.mm"
include "wb.mm"
include "zq.mm"
include "qden1elz.mm"
include "syl.mm"
include "mpbird.mm"
include "eqtrd.mm"
include "densq.mm"
include "3eqtr2rd.mm"
include "sq11d.mm"
include "mpbid.mm"

theorem zsqrtelqelz
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( ( A e. ZZ /\ ( sqrt ` A ) e. QQ ) -> ( sqrt ` A ) e. ZZ )

  proof
    cA
    cz
    wcel
    #
    cA
    csqrt
    cfv
    #
    cq
    wcel
    #
    wa
    #
    @1
    cdenom
    cfv
    #
    c1
    wceq
    #
    @1
    cz
    wcel
    #
    @3
    @4
    c1
    @3
    @4
    @2
    @4
    cn
    wcel
    @0
    @1
    qdencl
    adantl
    #
    nnred
    @3
    1red
    @3
    @4
    @3
    @4
    @7
    nnnn0d
    nn0ge0d
    cc0
    c1
    cle
    wbr
    @3
    0le1
    a1i
    @3
    c1
    c2
    cexp
    co
    #
    c1
    @1
    c2
    cexp
    co
    #
    cdenom
    cfv
    #
    @4
    c2
    cexp
    co
    #
    @8
    c1
    wceq
    @3
    sq1
    a1i
    @3
    @10
    cA
    cdenom
    cfv
    #
    c1
    @3
    @9
    cA
    cdenom
    @0
    @9
    cA
    wceq
    @2
    @0
    cA
    cA
    zcn
    sqsqrtd
    adantr
    fveq2d
    @3
    @12
    c1
    wceq
    #
    @0
    @0
    @2
    simpl
    @3
    cA
    cq
    wcel
    #
    @13
    @0
    wb
    @0
    @14
    @2
    cA
    zq
    adantr
    cA
    qden1elz
    syl
    mpbird
    eqtrd
    @2
    @10
    @11
    wceq
    @0
    @1
    densq
    adantl
    3eqtr2rd
    sq11d
    @2
    @5
    @6
    wb
    @0
    @1
    qden1elz
    adantl
    mpbid
end
