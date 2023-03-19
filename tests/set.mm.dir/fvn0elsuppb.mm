include "wcel.mm"
include "wfn.mm"
include "w3a.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "csupp.mm"
include "co.mm"
include "wi.mm"
include "fvn0elsupp.mm"
include "exp43.mm"
include "3imp.mm"
include "wa.mm"
include "cvv.mm"
include "wb.mm"
include "simp3.mm"
include "simp1.mm"
include "0ex.mm"
include "a1i.mm"
include "elsuppfn.mm"
include "syl3anc.mm"
include "simpr.mm"
include "syl6bi.mm"
include "impbid.mm"

theorem fvn0elsuppb
  let cB: class B
  let cG: class G
  let cV: class V
  let cX: class X


  assert |- ( ( B e. V /\ X e. B /\ G Fn B ) -> ( ( G ` X ) =/= (/) <-> X e. ( G supp (/) ) ) )

  proof
    cB
    cV
    wcel
    #
    cX
    cB
    wcel
    #
    cG
    cB
    wfn
    #
    w3a
    #
    cX
    cG
    cfv
    c0
    wne
    #
    cX
    cG
    c0
    csupp
    co
    wcel
    #
    @0
    @1
    @2
    @4
    @5
    wi
    @0
    @1
    @2
    @4
    @5
    cB
    cG
    cV
    cX
    fvn0elsupp
    exp43
    3imp
    @3
    @5
    @1
    @4
    wa
    #
    @4
    @3
    @2
    @0
    c0
    cvv
    wcel
    #
    @5
    @6
    wb
    @0
    @1
    @2
    simp3
    @0
    @1
    @2
    simp1
    @7
    @3
    0ex
    a1i
    cX
    cG
    cV
    cvv
    cB
    c0
    elsuppfn
    syl3anc
    @1
    @4
    simpr
    syl6bi
    impbid
end
