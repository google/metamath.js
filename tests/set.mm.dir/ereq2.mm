include "wceq.mm"
include "wrel.mm"
include "cdm.mm"
include "ccnv.mm"
include "ccom.mm"
include "cun.mm"
include "wss.mm"
include "w3a.mm"
include "wer.mm"
include "eqeq2.mm"
include "3anbi2d.mm"
include "df-er.mm"
include "3bitr4g.mm"

theorem ereq2
  let cA: class A
  let cB: class B
  let cR: class R


  assert |- ( A = B -> ( R Er A <-> R Er B ) )

  proof
    cA
    cB
    wceq
    #
    cR
    wrel
    #
    cR
    cdm
    #
    cA
    wceq
    #
    cR
    ccnv
    cR
    cR
    ccom
    cun
    cR
    wss
    #
    w3a
    @1
    @2
    cB
    wceq
    #
    @4
    w3a
    cA
    cR
    wer
    cB
    cR
    wer
    @0
    @3
    @5
    @1
    @4
    cA
    cB
    @2
    eqeq2
    3anbi2d
    cA
    cR
    df-er
    cB
    cR
    df-er
    3bitr4g
end
