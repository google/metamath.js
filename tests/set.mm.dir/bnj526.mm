include "wsbc.mm"
include "c0.mm"
include "cv.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "wceq.mm"
include "sbcbii.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "sbcie.mm"
include "3bitri.mm"

theorem bnj526
  let wph: wff ph
  let cA: class A
  let cR: class R
  let vf: setvar f
  let cG: class G
  let cX: class X
  let bnjwphn: wff ph"
  assume bnj526.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj526.2: |- ( ph" <-> [. G / f ]. ph )
  assume bnj526.3: |- G e. _V

  disjoint A f
  disjoint G f
  disjoint R f
  disjoint X f
  assert |- ( ph" <-> ( G ` (/) ) = _pred ( X , A , R ) )

  proof
    bnjwphn
    wph
    vf
    cG
    wsbc
    c0
    vf
    cv
    #
    cfv
    #
    cA
    cR
    cX
    c-bnj14
    #
    wceq
    #
    vf
    cG
    wsbc
    c0
    cG
    cfv
    #
    @2
    wceq
    #
    bnj526.2
    wph
    @3
    vf
    cG
    bnj526.1
    sbcbii
    @3
    @5
    vf
    cG
    bnj526.3
    @0
    cG
    wceq
    @1
    @4
    @2
    c0
    @0
    cG
    fveq1
    eqeq1d
    sbcie
    3bitri
end
