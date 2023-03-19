include "wsbc.mm"
include "c0.mm"
include "cfv.mm"
include "cv.mm"
include "c-bnj14.mm"
include "wceq.mm"
include "c1o.mm"
include "sbcbii.mm"
include "bnj105.mm"
include "bnj91.mm"
include "bnj95.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "sbcie.mm"
include "bitri.mm"

theorem bnj125
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cR: class R
  let vf: setvar f
  let vn: setvar n
  let cF: class F
  let bnjwphm: wff ph'
  let bnjwphn: wff ph"
  assume bnj125.1: |- ( ph <-> ( f ` (/) ) = _pred ( x , A , R ) )
  assume bnj125.2: |- ( ph' <-> [. 1o / n ]. ph )
  assume bnj125.3: |- ( ph" <-> [. F / f ]. ph' )
  assume bnj125.4: |- F = { <. (/) , _pred ( x , A , R ) >. }

  disjoint A f
  disjoint A n
  disjoint f n
  disjoint F f
  disjoint R f
  disjoint R n
  disjoint f x
  disjoint n x
  assert |- ( ph" <-> ( F ` (/) ) = _pred ( x , A , R ) )

  proof
    bnjwphn
    bnjwphm
    vf
    cF
    wsbc
    #
    c0
    cF
    cfv
    #
    cA
    cR
    vx
    cv
    c-bnj14
    #
    wceq
    #
    bnj125.3
    @0
    wph
    vn
    c1o
    wsbc
    #
    vf
    cF
    wsbc
    #
    @3
    bnjwphm
    @4
    vf
    cF
    bnj125.2
    sbcbii
    @5
    c0
    vf
    cv
    #
    cfv
    #
    @2
    wceq
    #
    vf
    cF
    wsbc
    @3
    @4
    @8
    vf
    cF
    wph
    vx
    vn
    cA
    cR
    vf
    c1o
    bnj125.1
    bnj105
    bnj91
    sbcbii
    @8
    @3
    vf
    cF
    vx
    cA
    cR
    cF
    bnj125.4
    bnj95
    @6
    cF
    wceq
    @7
    @1
    @2
    c0
    @6
    cF
    fveq1
    eqeq1d
    sbcie
    bitri
    bitri
    bitri
end
