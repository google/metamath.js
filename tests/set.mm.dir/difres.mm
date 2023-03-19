include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "cres.mm"
include "cdif.mm"
include "cin.mm"
include "df-res.mm"
include "difeq2i.mm"
include "c0.mm"
include "cun.mm"
include "difindi.mm"
include "wceq.mm"
include "ssdif.mm"
include "difid.mm"
include "syl6sseq.mm"
include "ss0.mm"
include "syl.mm"
include "uneq2d.mm"
include "syl5eq.mm"
include "un0.mm"
include "syl6eq.mm"

theorem difres
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A C_ ( B X. _V ) -> ( A \ ( C |` B ) ) = ( A \ C ) )

  proof
    cA
    cB
    cvv
    cxp
    #
    wss
    #
    cA
    cC
    cB
    cres
    #
    cdif
    cA
    cC
    @0
    cin
    #
    cdif
    #
    cA
    cC
    cdif
    #
    @2
    @3
    cA
    cC
    cB
    df-res
    difeq2i
    @1
    @4
    @5
    c0
    cun
    #
    @5
    @1
    @4
    @5
    cA
    @0
    cdif
    #
    cun
    @6
    cA
    cC
    @0
    difindi
    @1
    @7
    c0
    @5
    @1
    @7
    c0
    wss
    @7
    c0
    wceq
    @1
    @7
    @0
    @0
    cdif
    c0
    cA
    @0
    @0
    ssdif
    @0
    difid
    syl6sseq
    @7
    ss0
    syl
    uneq2d
    syl5eq
    @5
    un0
    syl6eq
    syl5eq
end
