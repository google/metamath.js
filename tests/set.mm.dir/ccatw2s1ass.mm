include "cword.mm"
include "wcel.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "wceq.mm"
include "id.mm"
include "s1cl.mm"
include "ccatass.mm"
include "syl3an.mm"

theorem ccatw2s1ass
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y


  assert |- ( ( W e. Word V /\ X e. V /\ Y e. V ) -> ( ( W ++ <" X "> ) ++ <" Y "> ) = ( W ++ ( <" X "> ++ <" Y "> ) ) )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    @1
    cX
    cV
    wcel
    cX
    cs1
    #
    @0
    wcel
    cY
    cV
    wcel
    cY
    cs1
    #
    @0
    wcel
    cW
    @2
    cconcat
    co
    @3
    cconcat
    co
    cW
    @2
    @3
    cconcat
    co
    cconcat
    co
    wceq
    @1
    id
    cX
    cV
    s1cl
    cY
    cV
    s1cl
    cV
    cW
    @2
    @3
    ccatass
    syl3an
end
