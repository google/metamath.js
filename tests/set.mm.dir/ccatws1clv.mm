include "cword.mm"
include "wcel.mm"
include "cvv.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "wrdv.mm"
include "s1cli.mm"
include "ccatcl.mm"
include "sylancl.mm"

theorem ccatws1clv
  let cV: class V
  let cW: class W
  let cX: class X


  assert |- ( W e. Word V -> ( W ++ <" X "> ) e. Word _V )

  proof
    cW
    cV
    cword
    wcel
    cW
    cvv
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
    cV
    cW
    wrdv
    cX
    s1cli
    cvv
    cW
    @1
    ccatcl
    sylancl
end
