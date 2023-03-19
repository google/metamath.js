include "wsbc.mm"
include "c0.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "wceq.mm"
include "cv.mm"
include "dfsbcq.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "sbcbii.mm"
include "vex.mm"
include "weq.mm"
include "sbcie.mm"
include "bitri.mm"
include "vtoclb.mm"

theorem bnj609
  let wph: wff ph
  let cA: class A
  let cR: class R
  let vf: setvar f
  let cG: class G
  let cX: class X
  let bnjwphn: wff ph"
  let ve: setvar e
  assume bnj609.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj609.2: |- ( ph" <-> [. G / f ]. ph )
  assume bnj609.3: |- G e. _V

  disjoint A f
  disjoint R f
  disjoint X f
  disjoint A e
  disjoint e f
  disjoint G e
  disjoint R e
  disjoint X e
  disjoint e ph
  assert |- ( ph" <-> ( G ` (/) ) = _pred ( X , A , R ) )

  proof
    bnjwphn
    wph
    vf
    cG
    wsbc
    #
    c0
    cG
    cfv
    #
    cA
    cR
    cX
    c-bnj14
    #
    wceq
    #
    bnj609.2
    wph
    vf
    ve
    cv
    #
    wsbc
    #
    c0
    @4
    cfv
    #
    @2
    wceq
    #
    @0
    @3
    ve
    cG
    bnj609.3
    wph
    vf
    @4
    cG
    dfsbcq
    @4
    cG
    wceq
    @6
    @1
    @2
    c0
    @4
    cG
    fveq1
    eqeq1d
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
    @4
    wsbc
    @7
    wph
    @10
    vf
    @4
    bnj609.1
    sbcbii
    @10
    @7
    vf
    @4
    ve
    vex
    vf
    ve
    weq
    @9
    @6
    @2
    c0
    @8
    @4
    fveq1
    eqeq1d
    sbcie
    bitri
    vtoclb
    bitri
end
