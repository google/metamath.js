include "cv.mm"
include "cec.mm"
include "c0.mm"
include "wne.mm"
include "cdm.mm"
include "wceq.mm"
include "cqs.mm"
include "eqid.mm"
include "neeq1.mm"
include "wcel.mm"
include "wa.mm"
include "eleq2.mm"
include "biimpar.mm"
include "ecdmn0.mm"
include "sylib.mm"
include "ectocld.mm"

theorem elqsn0
  let cA: class A
  let cB: class B
  let cR: class R
  let vx: setvar x


  assert |- ( ( dom R = A /\ B e. ( A /. R ) ) -> B =/= (/) )

  proof
    vx
    cv
    #
    cR
    cec
    #
    c0
    wne
    #
    cB
    c0
    wne
    cR
    cdm
    #
    cA
    wceq
    #
    vx
    cB
    cA
    cR
    cA
    cR
    cqs
    #
    @5
    eqid
    @1
    cB
    c0
    neeq1
    @4
    @0
    cA
    wcel
    #
    wa
    @0
    @3
    wcel
    #
    @2
    @4
    @7
    @6
    @3
    cA
    @0
    eleq2
    biimpar
    @0
    cR
    ecdmn0
    sylib
    ectocld
end
