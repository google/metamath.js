include "cz.mm"
include "cmap.mm"
include "co.mm"
include "cmpt.mm"
include "cmzp.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "c1.mm"
include "cneg.mm"
include "cmul.mm"
include "caddc.mm"
include "nfmpt1.mm"
include "nfel1.mm"
include "nfan.mm"
include "cv.mm"
include "wf.mm"
include "mzpf.mm"
include "ad2antlr.mm"
include "simpr.mm"
include "mptfcl.mm"
include "sylc.mm"
include "zcnd.mm"
include "mulm1d.mm"
include "oveq2d.mm"
include "ad2antrr.mm"
include "negsubd.mm"
include "eqtr2d.mm"
include "mpteq2da.mm"
include "cvv.mm"
include "elfvex.mm"
include "neg1z.mm"
include "mzpconstmpt.mm"
include "sylancl.mm"
include "mzpmulmpt.mm"
include "mpancom.mm"
include "mzpaddmpt.mm"
include "sylan2.mm"
include "eqeltrd.mm"

theorem mzpsubmpt
  let vx: setvar x
  let cA: class A
  let cB: class B
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
  assert |- ( ( ( x e. ( ZZ ^m V ) |-> A ) e. ( mzPoly ` V ) /\ ( x e. ( ZZ ^m V ) |-> B ) e. ( mzPoly ` V ) ) -> ( x e. ( ZZ ^m V ) |-> ( A - B ) ) e. ( mzPoly ` V ) )

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
    cB
    cmpt
    #
    @2
    wcel
    #
    wa
    #
    vx
    @0
    cA
    cB
    cmin
    co
    #
    cmpt
    vx
    @0
    cA
    c1
    cneg
    #
    cB
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    #
    @2
    @6
    vx
    @0
    @7
    @10
    @3
    @5
    vx
    vx
    @1
    @2
    vx
    @0
    cA
    nfmpt1
    nfel1
    vx
    @4
    @2
    vx
    @0
    cB
    nfmpt1
    nfel1
    nfan
    @6
    vx
    cv
    @0
    wcel
    #
    wa
    #
    @10
    cA
    cB
    cneg
    #
    caddc
    co
    @7
    @13
    @9
    @14
    cA
    caddc
    @13
    cB
    @13
    cB
    @13
    @0
    cz
    @4
    wf
    #
    @12
    cB
    cz
    wcel
    @5
    @15
    @3
    @12
    @4
    cV
    mzpf
    ad2antlr
    @6
    @12
    simpr
    #
    vx
    @0
    cB
    cz
    mptfcl
    sylc
    zcnd
    #
    mulm1d
    oveq2d
    @13
    cA
    cB
    @13
    cA
    @13
    @0
    cz
    @1
    wf
    #
    @12
    cA
    cz
    wcel
    @3
    @18
    @5
    @12
    @1
    cV
    mzpf
    ad2antrr
    @16
    vx
    @0
    cA
    cz
    mptfcl
    sylc
    zcnd
    @17
    negsubd
    eqtr2d
    mpteq2da
    @5
    @3
    vx
    @0
    @9
    cmpt
    @2
    wcel
    #
    @11
    @2
    wcel
    vx
    @0
    @8
    cmpt
    @2
    wcel
    #
    @5
    @19
    @5
    cV
    cvv
    wcel
    @8
    cz
    wcel
    @20
    @4
    cV
    cmzp
    elfvex
    neg1z
    vx
    @8
    cV
    mzpconstmpt
    sylancl
    vx
    @8
    cB
    cV
    mzpmulmpt
    mpancom
    vx
    cA
    @9
    cV
    mzpaddmpt
    sylan2
    eqeltrd
end
