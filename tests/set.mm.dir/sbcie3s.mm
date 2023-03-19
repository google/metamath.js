include "cv.mm"
include "wceq.mm"
include "cfv.mm"
include "wsbc.mm"
include "cvv.mm"
include "fvexd.mm"
include "wa.mm"
include "wb.mm"
include "simpllr.mm"
include "fveq2.mm"
include "ad3antrrr.mm"
include "eqtrd.mm"
include "syl6eqr.mm"
include "simplr.mm"
include "simpr.mm"
include "syl3anc.mm"
include "bicomd.mm"
include "sbcied.mm"

theorem sbcie3s
  let wph: wff ph
  let wps: wff ps
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cE: class E
  let cF: class F
  let cG: class G
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume sbcie3s.a: |- A = ( E ` W )
  assume sbcie3s.b: |- B = ( F ` W )
  assume sbcie3s.c: |- C = ( G ` W )
  assume sbcie3s.1: |- ( ( a = A /\ b = B /\ c = C ) -> ( ph <-> ps ) )

  disjoint a b
  disjoint a c
  disjoint a w
  disjoint b c
  disjoint b w
  disjoint c w
  disjoint E a
  disjoint E b
  disjoint E c
  disjoint F b
  disjoint F c
  disjoint G c
  disjoint W a
  disjoint W b
  disjoint W c
  disjoint a ph
  disjoint b ph
  disjoint c ph
  assert |- ( w = W -> ( [. ( E ` w ) / a ]. [. ( F ` w ) / b ]. [. ( G ` w ) / c ]. ps <-> ph ) )

  proof
    vw
    cv
    #
    cW
    wceq
    #
    wps
    vc
    @0
    cG
    cfv
    #
    wsbc
    #
    vb
    @0
    cF
    cfv
    #
    wsbc
    wph
    va
    @0
    cE
    cfv
    #
    cvv
    @1
    @0
    cE
    fvexd
    @1
    va
    cv
    #
    @5
    wceq
    #
    wa
    #
    @3
    wph
    vb
    @4
    cvv
    @8
    @0
    cF
    fvexd
    @8
    vb
    cv
    #
    @4
    wceq
    #
    wa
    #
    wps
    wph
    vc
    @2
    cvv
    @11
    @0
    cG
    fvexd
    @11
    vc
    cv
    #
    @2
    wceq
    #
    wa
    #
    wph
    wps
    @14
    @6
    cA
    wceq
    @9
    cB
    wceq
    @12
    cC
    wceq
    wph
    wps
    wb
    @14
    @6
    cW
    cE
    cfv
    #
    cA
    @14
    @6
    @5
    @15
    @1
    @7
    @10
    @13
    simpllr
    @1
    @5
    @15
    wceq
    @7
    @10
    @13
    @0
    cW
    cE
    fveq2
    ad3antrrr
    eqtrd
    sbcie3s.a
    syl6eqr
    @14
    @9
    cW
    cF
    cfv
    #
    cB
    @14
    @9
    @4
    @16
    @8
    @10
    @13
    simplr
    @1
    @4
    @16
    wceq
    @7
    @10
    @13
    @0
    cW
    cF
    fveq2
    ad3antrrr
    eqtrd
    sbcie3s.b
    syl6eqr
    @14
    @12
    cW
    cG
    cfv
    #
    cC
    @14
    @12
    @2
    @17
    @11
    @13
    simpr
    @1
    @2
    @17
    wceq
    @7
    @10
    @13
    @0
    cW
    cG
    fveq2
    ad3antrrr
    eqtrd
    sbcie3s.c
    syl6eqr
    sbcie3s.1
    syl3anc
    bicomd
    sbcied
    sbcied
    sbcied
end
