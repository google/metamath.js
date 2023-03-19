include "cvv.mm"
include "wcel.mm"
include "cmzp.mm"
include "cfv.mm"
include "cmzpcl.mm"
include "cz.mm"
include "cmap.mm"
include "co.mm"
include "csn.mm"
include "cxp.mm"
include "mzpincl.mm"
include "mzpcl1.mm"
include "sylan.mm"

theorem mzpconst
  let cC: class C
  let cV: class V


  assert |- ( ( V e. _V /\ C e. ZZ ) -> ( ( ZZ ^m V ) X. { C } ) e. ( mzPoly ` V ) )

  proof
    cV
    cvv
    wcel
    cV
    cmzp
    cfv
    #
    cV
    cmzpcl
    cfv
    wcel
    cC
    cz
    wcel
    cz
    cV
    cmap
    co
    cC
    csn
    cxp
    @0
    wcel
    cV
    mzpincl
    @0
    cC
    cV
    mzpcl1
    sylan
end
