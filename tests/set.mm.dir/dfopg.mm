include "wcel.mm"
include "cvv.mm"
include "cop.mm"
include "csn.mm"
include "cpr.mm"
include "wceq.mm"
include "elex.mm"
include "wa.mm"
include "c0.mm"
include "cif.mm"
include "dfopif.mm"
include "iftrue.mm"
include "syl5eq.mm"
include "syl2an.mm"

theorem dfopg
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W


  assert |- ( ( A e. V /\ B e. W ) -> <. A , B >. = { { A } , { A , B } } )

  proof
    cA
    cV
    wcel
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    cA
    cB
    cop
    #
    cA
    csn
    cA
    cB
    cpr
    cpr
    #
    wceq
    cB
    cW
    wcel
    cA
    cV
    elex
    cB
    cW
    elex
    @0
    @1
    wa
    #
    @2
    @4
    @3
    c0
    cif
    @3
    cA
    cB
    dfopif
    @4
    @3
    c0
    iftrue
    syl5eq
    syl2an
end
