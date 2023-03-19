include "cz.mm"
include "cmap.mm"
include "co.mm"
include "cmpt.mm"
include "cmzp.mm"
include "cfv.mm"
include "wcel.mm"
include "cneg.mm"
include "cc0.mm"
include "cmin.mm"
include "df-neg.mm"
include "mpteq2i.mm"
include "cvv.mm"
include "elfvex.mm"
include "0z.mm"
include "mzpconstmpt.mm"
include "sylancl.mm"
include "mzpsubmpt.mm"
include "mpancom.mm"
include "syl5eqel.mm"

theorem mzpnegmpt
  let vx: setvar x
  let cA: class A
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let cC: class C
  let cD: class D

  disjoint V x
  disjoint V a
  disjoint V b
  disjoint a x
  disjoint b x
  disjoint a b
  disjoint C x
  disjoint D x
  disjoint D a
  disjoint D b
  disjoint A a
  disjoint A b
  assert |- ( ( x e. ( ZZ ^m V ) |-> A ) e. ( mzPoly ` V ) -> ( x e. ( ZZ ^m V ) |-> -u A ) e. ( mzPoly ` V ) )

  proof
    vx
    cz
    cV
    cmap
    co
    #
    cA
    cmpt
    #
    cV
    cmzp
    cfv
    #
    wcel
    #
    vx
    @0
    cA
    cneg
    #
    cmpt
    vx
    @0
    cc0
    cA
    cmin
    co
    #
    cmpt
    #
    @2
    vx
    @0
    @4
    @5
    cA
    df-neg
    mpteq2i
    vx
    @0
    cc0
    cmpt
    @2
    wcel
    #
    @3
    @6
    @2
    wcel
    @3
    cV
    cvv
    wcel
    cc0
    cz
    wcel
    @7
    @1
    cV
    cmzp
    elfvex
    0z
    vx
    cc0
    cV
    mzpconstmpt
    sylancl
    vx
    cc0
    cA
    cV
    mzpsubmpt
    mpancom
    syl5eqel
end
