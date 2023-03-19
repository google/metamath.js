include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "csn.mm"
include "ccnv.mm"
include "cnvcnvsn.mm"
include "wrel.mm"
include "wceq.mm"
include "relsnopg.mm"
include "ancoms.mm"
include "dfrel2.mm"
include "sylib.mm"
include "syl5eqr.mm"

theorem cnvsng
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> `' { <. A , B >. } = { <. B , A >. } )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    #
    cA
    cB
    cop
    csn
    ccnv
    cB
    cA
    cop
    csn
    #
    ccnv
    ccnv
    #
    @3
    cB
    cA
    cnvcnvsn
    @2
    @3
    wrel
    #
    @4
    @3
    wceq
    @1
    @0
    @5
    cB
    cA
    cW
    cV
    relsnopg
    ancoms
    @3
    dfrel2
    sylib
    syl5eqr
end
