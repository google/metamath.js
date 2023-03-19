include "wcel.mm"
include "cs1.mm"
include "cword.mm"
include "cconcat.mm"
include "co.mm"
include "s1cl.mm"
include "ccatws1cl.mm"
include "sylan.mm"

theorem ccat2s1cl
  let cV: class V
  let cX: class X
  let cY: class Y


  assert |- ( ( X e. V /\ Y e. V ) -> ( <" X "> ++ <" Y "> ) e. Word V )

  proof
    cX
    cV
    wcel
    cX
    cs1
    #
    cV
    cword
    #
    wcel
    cY
    cV
    wcel
    @0
    cY
    cs1
    cconcat
    co
    @1
    wcel
    cX
    cV
    s1cl
    cV
    @0
    cY
    ccatws1cl
    sylan
end
