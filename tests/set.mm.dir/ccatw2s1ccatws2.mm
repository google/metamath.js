include "cword.mm"
include "wcel.mm"
include "w3a.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "cs2.mm"
include "ccatw2s1ass.mm"
include "wceq.mm"
include "df-s2.mm"
include "a1i.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem ccatw2s1ccatws2
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y


  assert |- ( ( W e. Word V /\ X e. V /\ Y e. V ) -> ( ( W ++ <" X "> ) ++ <" Y "> ) = ( W ++ <" X Y "> ) )

  proof
    cW
    cV
    cword
    wcel
    cX
    cV
    wcel
    cY
    cV
    wcel
    w3a
    #
    cW
    cX
    cs1
    #
    cconcat
    co
    cY
    cs1
    #
    cconcat
    co
    cW
    @1
    @2
    cconcat
    co
    #
    cconcat
    co
    cW
    cX
    cY
    cs2
    #
    cconcat
    co
    cV
    cW
    cX
    cY
    ccatw2s1ass
    @0
    @3
    @4
    cW
    cconcat
    @0
    @4
    @3
    @4
    @3
    wceq
    @0
    cX
    cY
    df-s2
    a1i
    eqcomd
    oveq2d
    eqtrd
end
