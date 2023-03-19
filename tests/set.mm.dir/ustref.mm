include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "cid.mm"
include "cres.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "eqid.mm"
include "resieq.mm"
include "mpbiri.mm"
include "anidms.mm"
include "3ad2ant3.mm"
include "wi.mm"
include "ustdiag.mm"
include "ssbrd.mm"
include "3adant3.mm"
include "mpd.mm"

theorem ustref
  let cA: class A
  let cU: class U
  let cV: class V
  let cX: class X


  assert |- ( ( U e. ( UnifOn ` X ) /\ V e. U /\ A e. X ) -> A V A )

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
    cA
    cA
    cid
    cX
    cres
    #
    wbr
    #
    cA
    cA
    cV
    wbr
    #
    @2
    @0
    @4
    @1
    @2
    @4
    @2
    @2
    wa
    @4
    cA
    cA
    wceq
    cA
    eqid
    cX
    cA
    cA
    resieq
    mpbiri
    anidms
    3ad2ant3
    @0
    @1
    @4
    @5
    wi
    @2
    @0
    @1
    wa
    @3
    cV
    cA
    cA
    cU
    cV
    cX
    ustdiag
    ssbrd
    3adant3
    mpd
end
