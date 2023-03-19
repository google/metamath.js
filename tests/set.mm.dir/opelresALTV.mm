include "cop.mm"
include "cres.mm"
include "wcel.mm"
include "cvv.mm"
include "cxp.mm"
include "wa.mm"
include "df-res.mm"
include "elin2.mm"
include "elex.mm"
include "biantrud.mm"
include "opelxp.mm"
include "syl6rbbr.mm"
include "anbi1cd.mm"
include "syl5bb.mm"

theorem opelresALTV
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cV: class V


  assert |- ( C e. V -> ( <. B , C >. e. ( R |` A ) <-> ( B e. A /\ <. B , C >. e. R ) ) )

  proof
    cB
    cC
    cop
    #
    cR
    cA
    cres
    #
    wcel
    @0
    cR
    wcel
    #
    @0
    cA
    cvv
    cxp
    #
    wcel
    #
    wa
    cC
    cV
    wcel
    #
    cB
    cA
    wcel
    #
    @2
    wa
    @0
    cR
    @3
    @1
    cR
    cA
    df-res
    elin2
    @5
    @4
    @6
    @2
    @5
    @6
    @6
    cC
    cvv
    wcel
    #
    wa
    @4
    @5
    @7
    @6
    cC
    cV
    elex
    biantrud
    cB
    cC
    cA
    cvv
    opelxp
    syl6rbbr
    anbi1cd
    syl5bb
end
