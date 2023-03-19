include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cmat.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "cvv.mm"
include "eqid.mm"
include "cfn.mm"
include "matrcl.mm"
include "simpld.mm"
include "ssfi.mm"
include "sylan.mm"
include "simprd.mm"
include "adantr.mm"
include "w3a.mm"
include "wi.mm"
include "ssel.mm"
include "adantl.mm"
include "imp.mm"
include "3adant3.mm"
include "3adant2.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "3ad2ant1.mm"
include "matecl.mm"
include "syl3anc.mm"
include "matbas2d.mm"

theorem submabas
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let vi: setvar i
  let vj: setvar j
  let cM: class M
  let cN: class N
  assume submabas.a: |- A = ( N Mat R )
  assume submabas.b: |- B = ( Base ` A )

  disjoint B i
  disjoint B j
  disjoint i j
  disjoint D i
  disjoint D j
  disjoint M i
  disjoint M j
  disjoint N i
  disjoint N j
  disjoint R i
  disjoint R j
  assert |- ( ( M e. B /\ D C_ N ) -> ( i e. D , j e. D |-> ( i M j ) ) e. ( Base ` ( D Mat R ) ) )

  proof
    cM
    cB
    wcel
    #
    cD
    cN
    wss
    #
    wa
    #
    vi
    vj
    cD
    cR
    cmat
    co
    #
    @3
    cbs
    cfv
    #
    vi
    cv
    #
    vj
    cv
    #
    cM
    co
    #
    cR
    cR
    cbs
    cfv
    #
    cD
    cvv
    @3
    eqid
    @8
    eqid
    #
    @4
    eqid
    @0
    cN
    cfn
    wcel
    #
    @1
    cD
    cfn
    wcel
    @0
    @10
    cR
    cvv
    wcel
    #
    cA
    cB
    cR
    cN
    cM
    submabas.a
    submabas.b
    matrcl
    #
    simpld
    cN
    cD
    ssfi
    sylan
    @0
    @11
    @1
    @0
    @10
    @11
    @12
    simprd
    adantr
    @2
    @5
    cD
    wcel
    #
    @6
    cD
    wcel
    #
    w3a
    @5
    cN
    wcel
    #
    @6
    cN
    wcel
    #
    cM
    cA
    cbs
    cfv
    #
    wcel
    #
    @7
    @8
    wcel
    @2
    @13
    @15
    @14
    @2
    @13
    @15
    @1
    @13
    @15
    wi
    @0
    cD
    cN
    @5
    ssel
    adantl
    imp
    3adant3
    @2
    @14
    @16
    @13
    @2
    @14
    @16
    @1
    @14
    @16
    wi
    @0
    cD
    cN
    @6
    ssel
    adantl
    imp
    3adant2
    @2
    @13
    @18
    @14
    @0
    @18
    @1
    @0
    @18
    cB
    @17
    cM
    submabas.b
    eleq2i
    biimpi
    adantr
    3ad2ant1
    cA
    cR
    @5
    @6
    @8
    cM
    cN
    submabas.a
    @9
    matecl
    syl3anc
    matbas2d
end
