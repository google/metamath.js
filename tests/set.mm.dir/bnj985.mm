include "wcel.mm"
include "wex.mm"
include "wsbc.mm"
include "cvv.mm"
include "wb.mm"
include "bnj918.mm"
include "bnj984.mm"
include "ax-mp.mm"
include "sbcex2.mm"
include "cv.mm"
include "wsb.mm"
include "nfv.mm"
include "sb8e.mm"
include "sbsbc.mm"
include "exbii.mm"
include "bitri.mm"
include "bnj133.mm"
include "sbcbii.mm"
include "3bitr4i.mm"

theorem bnj985
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let cB: class B
  let cC: class C
  let cD: class D
  let vf: setvar f
  let vn: setvar n
  let cG: class G
  let vp: setvar p
  let bnjwchm: wff ch'
  let bnjwchn: wff ch"
  assume bnj985.3: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )
  assume bnj985.6: |- ( ch' <-> [. p / n ]. ch )
  assume bnj985.9: |- ( ch" <-> [. G / f ]. ch' )
  assume bnj985.11: |- B = { f | E. n e. D ( f Fn n /\ ph /\ ps ) }
  assume bnj985.13: |- G = ( f u. { <. n , C >. } )

  disjoint G p
  disjoint ch p
  disjoint f p
  assert |- ( G e. B <-> E. p ch" )

  proof
    cG
    cB
    wcel
    #
    wch
    vn
    wex
    #
    vf
    cG
    wsbc
    #
    bnjwchn
    vp
    wex
    #
    cG
    cvv
    wcel
    @0
    @2
    wb
    cC
    vf
    vn
    cG
    bnj985.13
    bnj918
    wph
    wps
    wch
    cvv
    cB
    cD
    vf
    vn
    cG
    bnj985.3
    bnj985.11
    bnj984
    ax-mp
    bnjwchm
    vp
    wex
    #
    vf
    cG
    wsbc
    bnjwchm
    vf
    cG
    wsbc
    #
    vp
    wex
    @2
    @3
    bnjwchm
    vp
    vf
    cG
    sbcex2
    @1
    @4
    vf
    cG
    @1
    wch
    vn
    vp
    cv
    wsbc
    #
    bnjwchm
    vp
    @1
    wch
    vn
    vp
    wsb
    #
    vp
    wex
    @6
    vp
    wex
    wch
    vn
    vp
    wch
    vp
    nfv
    sb8e
    @7
    @6
    vp
    wch
    vn
    vp
    sbsbc
    exbii
    bitri
    bnj985.6
    bnj133
    sbcbii
    bnjwchn
    @5
    vp
    bnj985.9
    exbii
    3bitr4i
    bitri
end
