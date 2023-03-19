include "cdm.mm"
include "wceq.mm"
include "cec.mm"
include "cqs.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "elqsn0.mm"
include "ecdmn0.mm"
include "sylibr.mm"
include "simpl.mm"
include "eleqtrd.mm"

theorem ecelqsdm
  let cA: class A
  let cB: class B
  let cR: class R


  assert |- ( ( dom R = A /\ [ B ] R e. ( A /. R ) ) -> B e. A )

  proof
    cR
    cdm
    #
    cA
    wceq
    #
    cB
    cR
    cec
    #
    cA
    cR
    cqs
    wcel
    #
    wa
    #
    cB
    @0
    cA
    @4
    @2
    c0
    wne
    cB
    @0
    wcel
    cA
    @2
    cR
    elqsn0
    cB
    cR
    ecdmn0
    sylibr
    @1
    @3
    simpl
    eleqtrd
end
