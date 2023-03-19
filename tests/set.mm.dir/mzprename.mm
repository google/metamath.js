include "cvv.mm"
include "wcel.mm"
include "cmzp.mm"
include "cfv.mm"
include "wf.mm"
include "w3a.mm"
include "cz.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "wb.mm"
include "zex.mm"
include "simpll.mm"
include "elmapg.mm"
include "sylancr.mm"
include "mpbid.mm"
include "simplr.mm"
include "fcompt.mm"
include "syl2anc.mm"
include "fveq1.mm"
include "eqid.mm"
include "fvex.mm"
include "fvmpt.mm"
include "ad2antlr.mm"
include "eqcomd.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "3adant2.mm"
include "wral.mm"
include "simpl1.mm"
include "ffvelrn.mm"
include "3ad2antl3.mm"
include "mzpproj.mm"
include "ralrimiva.mm"
include "mzpsubst.mm"
include "syld3an3.mm"
include "eqeltrd.mm"

theorem mzprename
  let vx: setvar x
  let cR: class R
  let cF: class F
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b

  disjoint W x
  disjoint F x
  disjoint R x
  disjoint V x
  disjoint W a
  disjoint W b
  disjoint a x
  disjoint b x
  disjoint a b
  disjoint F a
  disjoint F b
  disjoint R a
  disjoint R b
  disjoint V a
  assert |- ( ( W e. _V /\ F e. ( mzPoly ` V ) /\ R : V --> W ) -> ( x e. ( ZZ ^m W ) |-> ( F ` ( x o. R ) ) ) e. ( mzPoly ` W ) )

  proof
    cW
    cvv
    wcel
    #
    cF
    cV
    cmzp
    cfv
    wcel
    #
    cV
    cW
    cR
    wf
    #
    w3a
    #
    vx
    cz
    cW
    cmap
    co
    #
    vx
    cv
    #
    cR
    ccom
    #
    cF
    cfv
    #
    cmpt
    #
    vx
    @4
    va
    cV
    @5
    vb
    @4
    va
    cv
    #
    cR
    cfv
    #
    vb
    cv
    #
    cfv
    #
    cmpt
    #
    cfv
    #
    cmpt
    #
    cF
    cfv
    #
    cmpt
    #
    cW
    cmzp
    cfv
    #
    @0
    @2
    @8
    @17
    wceq
    @1
    @0
    @2
    wa
    #
    vx
    @4
    @7
    @16
    @19
    @5
    @4
    wcel
    #
    wa
    #
    @6
    @15
    cF
    @21
    @6
    va
    cV
    @10
    @5
    cfv
    #
    cmpt
    #
    @15
    @21
    cW
    cz
    @5
    wf
    #
    @2
    @6
    @23
    wceq
    @21
    @20
    @24
    @19
    @20
    simpr
    @21
    cz
    cvv
    wcel
    @0
    @20
    @24
    wb
    zex
    @0
    @2
    @20
    simpll
    cz
    cW
    @5
    cvv
    cvv
    elmapg
    sylancr
    mpbid
    @0
    @2
    @20
    simplr
    va
    @5
    cR
    cV
    cW
    cz
    fcompt
    syl2anc
    @21
    va
    cV
    @22
    @14
    @21
    @9
    cV
    wcel
    #
    wa
    @14
    @22
    @20
    @14
    @22
    wceq
    @19
    @25
    vb
    @5
    @12
    @22
    @4
    @13
    @10
    @11
    @5
    fveq1
    @13
    eqid
    @10
    @5
    fvex
    fvmpt
    ad2antlr
    eqcomd
    mpteq2dva
    eqtrd
    fveq2d
    mpteq2dva
    3adant2
    @0
    @1
    @2
    @13
    @18
    wcel
    #
    va
    cV
    wral
    @17
    @18
    wcel
    @3
    @26
    va
    cV
    @3
    @25
    wa
    @0
    @10
    cW
    wcel
    #
    @26
    @0
    @1
    @2
    @25
    simpl1
    @2
    @0
    @25
    @27
    @1
    cV
    cW
    @9
    cR
    ffvelrn
    3ad2antl3
    vb
    cW
    @10
    mzpproj
    syl2anc
    ralrimiva
    vx
    va
    cF
    @13
    cV
    cW
    mzpsubst
    syld3an3
    eqeltrd
end
