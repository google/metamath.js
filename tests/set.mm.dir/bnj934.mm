include "c0.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "c-bnj14.mm"
include "eqtr.mm"
include "sylan2b.mm"
include "wsbc.mm"
include "vex.mm"
include "bnj523.mm"
include "bitr4i.mm"
include "sbcbii.mm"
include "bitri.mm"
include "bnj609.mm"
include "sylibr.mm"
include "ancoms.mm"

theorem bnj934
  let wph: wff ph
  let cA: class A
  let cR: class R
  let vf: setvar f
  let vn: setvar n
  let cG: class G
  let cX: class X
  let vp: setvar p
  let bnjwphm: wff ph'
  let bnjwphn: wff ph"
  assume bnj934.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj934.4: |- ( ph' <-> [. p / n ]. ph )
  assume bnj934.7: |- ( ph" <-> [. G / f ]. ph' )
  assume bnj934.50: |- G e. _V

  disjoint A f
  disjoint A n
  disjoint f n
  disjoint R f
  disjoint R n
  disjoint X f
  disjoint X n
  assert |- ( ( ph /\ ( G ` (/) ) = ( f ` (/) ) ) -> ph" )

  proof
    c0
    cG
    cfv
    #
    c0
    vf
    cv
    #
    cfv
    #
    wceq
    #
    wph
    bnjwphn
    @3
    wph
    wa
    @0
    cA
    cR
    cX
    c-bnj14
    #
    wceq
    #
    bnjwphn
    wph
    @3
    @2
    @4
    wceq
    #
    @5
    bnj934.1
    @0
    @2
    @4
    eqtr
    sylan2b
    wph
    cA
    cR
    vf
    cG
    cX
    bnjwphn
    bnj934.1
    bnjwphn
    bnjwphm
    vf
    cG
    wsbc
    wph
    vf
    cG
    wsbc
    bnj934.7
    bnjwphm
    wph
    vf
    cG
    bnjwphm
    @6
    wph
    wph
    cA
    cR
    vn
    @1
    vp
    cv
    cX
    bnjwphm
    bnj934.1
    bnj934.4
    vp
    vex
    bnj523
    bnj934.1
    bitr4i
    sbcbii
    bitri
    bnj934.50
    bnj609
    sylibr
    ancoms
end
