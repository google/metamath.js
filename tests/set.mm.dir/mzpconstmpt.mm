include "cvv.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cmap.mm"
include "co.mm"
include "cmpt.mm"
include "csn.mm"
include "cxp.mm"
include "cmzp.mm"
include "cfv.mm"
include "fconstmpt.mm"
include "mzpconst.mm"
include "syl5eqelr.mm"

theorem mzpconstmpt
  let vx: setvar x
  let cC: class C
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let cD: class D
  let cA: class A

  disjoint V x
  disjoint C x
  disjoint V a
  disjoint V b
  disjoint a x
  disjoint b x
  disjoint a b
  disjoint D x
  disjoint D a
  disjoint D b
  disjoint A a
  disjoint A b
  assert |- ( ( V e. _V /\ C e. ZZ ) -> ( x e. ( ZZ ^m V ) |-> C ) e. ( mzPoly ` V ) )

  proof
    cV
    cvv
    wcel
    cC
    cz
    wcel
    wa
    vx
    cz
    cV
    cmap
    co
    #
    cC
    cmpt
    @0
    cC
    csn
    cxp
    cV
    cmzp
    cfv
    vx
    @0
    cC
    fconstmpt
    cC
    cV
    mzpconst
    syl5eqelr
end
