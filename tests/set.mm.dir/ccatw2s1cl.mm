include "cword.mm"
include "wcel.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "ccatws1cl.mm"
include "stoic3.mm"

theorem ccatw2s1cl
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y


  assert |- ( ( W e. Word V /\ X e. V /\ Y e. V ) -> ( ( W ++ <" X "> ) ++ <" Y "> ) e. Word V )

  proof
    cW
    cV
    cword
    #
    wcel
    cX
    cV
    wcel
    cW
    cX
    cs1
    cconcat
    co
    #
    @0
    wcel
    cY
    cV
    wcel
    @1
    cY
    cs1
    cconcat
    co
    @0
    wcel
    cV
    cW
    cX
    ccatws1cl
    cV
    @1
    cY
    ccatws1cl
    stoic3
end
