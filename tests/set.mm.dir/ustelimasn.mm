include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "cop.mm"
include "csn.mm"
include "cima.mm"
include "simp3.mm"
include "cid.mm"
include "cres.mm"
include "wss.mm"
include "ustdiag.mm"
include "3adant3.mm"
include "opelresi.mm"
include "ibir.mm"
include "3ad2ant3.mm"
include "sseldd.mm"
include "wb.mm"
include "elimasng.mm"
include "anidms.mm"
include "biimpar.mm"
include "syl2anc.mm"

theorem ustelimasn
  let cA: class A
  let cU: class U
  let cV: class V
  let cX: class X


  assert |- ( ( U e. ( UnifOn ` X ) /\ V e. U /\ A e. X ) -> A e. ( V " { A } ) )

  proof
    cU
    cX
    cust
    cfv
    wcel
    #
    cV
    cU
    wcel
    #
    cA
    cX
    wcel
    #
    w3a
    #
    @2
    cA
    cA
    cop
    #
    cV
    wcel
    #
    cA
    cV
    cA
    csn
    cima
    wcel
    #
    @0
    @1
    @2
    simp3
    @3
    cid
    cX
    cres
    #
    cV
    @4
    @0
    @1
    @7
    cV
    wss
    @2
    cU
    cV
    cX
    ustdiag
    3adant3
    @2
    @0
    @4
    @7
    wcel
    #
    @1
    @2
    @8
    cA
    cX
    cX
    opelresi
    ibir
    3ad2ant3
    sseldd
    @2
    @6
    @5
    @2
    @6
    @5
    wb
    cV
    cA
    cA
    cX
    cX
    elimasng
    anidms
    biimpar
    syl2anc
end
