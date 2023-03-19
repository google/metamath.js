include "wcel.mm"
include "cv.mm"
include "wfn.mm"
include "w3a.mm"
include "wrex.mm"
include "wsbc.mm"
include "wex.mm"
include "cab.mm"
include "sbc8g.mm"
include "eleq2i.mm"
include "syl6rbbr.mm"
include "wa.mm"
include "df-rex.mm"
include "w-bnj17.mm"
include "bnj252.mm"
include "bitri.mm"
include "bnj133.mm"
include "sbcbii.mm"
include "syl6bb.mm"

theorem bnj984
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let cA: class A
  let cB: class B
  let cD: class D
  let vf: setvar f
  let vn: setvar n
  let cG: class G
  assume bnj984.3: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )
  assume bnj984.11: |- B = { f | E. n e. D ( f Fn n /\ ph /\ ps ) }


  assert |- ( G e. A -> ( G e. B <-> [. G / f ]. E. n ch ) )

  proof
    cG
    cA
    wcel
    #
    cG
    cB
    wcel
    #
    vf
    cv
    vn
    cv
    #
    wfn
    #
    wph
    wps
    w3a
    #
    vn
    cD
    wrex
    #
    vf
    cG
    wsbc
    #
    wch
    vn
    wex
    #
    vf
    cG
    wsbc
    @0
    @6
    cG
    @5
    vf
    cab
    #
    wcel
    @1
    @5
    vf
    cG
    cA
    sbc8g
    cB
    @8
    cG
    bnj984.11
    eleq2i
    syl6rbbr
    @5
    @7
    vf
    cG
    @5
    @2
    cD
    wcel
    #
    @4
    wa
    #
    wch
    vn
    @4
    vn
    cD
    df-rex
    wch
    @9
    @3
    wph
    wps
    w-bnj17
    @10
    bnj984.3
    @9
    @3
    wph
    wps
    bnj252
    bitri
    bnj133
    sbcbii
    syl6bb
end
