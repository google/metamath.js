include "wcel.mm"
include "cop.mm"
include "cid.mm"
include "cres.mm"
include "wbr.mm"
include "ididg.mm"
include "df-br.mm"
include "sylib.mm"
include "opelresg.mm"
include "mpbirand.mm"

theorem opelresi
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( A e. V -> ( <. A , A >. e. ( _I |` B ) <-> A e. B ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cA
    cop
    #
    cid
    cB
    cres
    wcel
    @1
    cid
    wcel
    #
    cA
    cB
    wcel
    @0
    cA
    cA
    cid
    wbr
    @2
    cA
    cV
    ididg
    cA
    cA
    cid
    df-br
    sylib
    cA
    cA
    cid
    cB
    cV
    opelresg
    mpbirand
end
