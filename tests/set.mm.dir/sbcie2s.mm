include "cv.mm"
include "wceq.mm"
include "cfv.mm"
include "fvex.mm"
include "wa.mm"
include "wb.mm"
include "simprl.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "adantr.mm"
include "eqtrd.mm"
include "simprr.mm"
include "syl2anc.mm"
include "bicomd.mm"
include "ex.mm"
include "sbc2iedv.mm"

theorem sbcie2s
  let wph: wff ph
  let wps: wff ps
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cE: class E
  let cF: class F
  let cW: class W
  let va: setvar a
  let vb: setvar b
  assume sbcie2s.a: |- A = ( E ` W )
  assume sbcie2s.b: |- B = ( F ` W )
  assume sbcie2s.1: |- ( ( a = A /\ b = B ) -> ( ph <-> ps ) )

  disjoint a b
  disjoint a w
  disjoint b w
  disjoint E a
  disjoint E b
  disjoint F b
  disjoint W a
  disjoint W b
  disjoint a ph
  disjoint b ph
  assert |- ( w = W -> ( [. ( E ` w ) / a ]. [. ( F ` w ) / b ]. ps <-> ph ) )

  proof
    vw
    cv
    #
    cW
    wceq
    #
    wps
    wph
    va
    vb
    @0
    cE
    cfv
    #
    @0
    cF
    cfv
    #
    @0
    cE
    fvex
    @0
    cF
    fvex
    @1
    va
    cv
    #
    @2
    wceq
    #
    vb
    cv
    #
    @3
    wceq
    #
    wa
    #
    wps
    wph
    wb
    @1
    @8
    wa
    #
    wph
    wps
    @9
    @4
    cA
    wceq
    @6
    cB
    wceq
    wph
    wps
    wb
    @9
    @4
    @2
    cA
    @1
    @5
    @7
    simprl
    @1
    @2
    cA
    wceq
    @8
    @1
    @2
    cW
    cE
    cfv
    cA
    @0
    cW
    cE
    fveq2
    sbcie2s.a
    syl6eqr
    adantr
    eqtrd
    @9
    @6
    @3
    cB
    @1
    @5
    @7
    simprr
    @1
    @3
    cB
    wceq
    @8
    @1
    @3
    cW
    cF
    cfv
    cB
    @0
    cW
    cF
    fveq2
    sbcie2s.b
    syl6eqr
    adantr
    eqtrd
    sbcie2s.1
    syl2anc
    bicomd
    ex
    sbc2iedv
end
