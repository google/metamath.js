include "wcel.mm"
include "cword.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "s1cl.mm"
include "ccatcl.mm"
include "sylan2.mm"

theorem ccatws1cl
  let cV: class V
  let cW: class W
  let cX: class X


  assert |- ( ( W e. Word V /\ X e. V ) -> ( W ++ <" X "> ) e. Word V )

  proof
    cX
    cV
    wcel
    cW
    cV
    cword
    #
    wcel
    cX
    cs1
    #
    @0
    wcel
    cW
    @1
    cconcat
    co
    @0
    wcel
    cX
    cV
    s1cl
    cV
    cW
    @1
    ccatcl
    sylan2
end
