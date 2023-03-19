include "cab.mm"
include "cint.mm"
include "ccnv.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cvv.mm"
include "cxp.mm"
include "cpw.mm"
include "crab.mm"
include "wcel.mm"
include "wel.mm"
include "wi.mm"
include "wal.mm"
include "cin.mm"
include "cnvcnv.mm"
include "eleq2i.mm"
include "elin.mm"
include "rbaib.mm"
include "syl5bb.mm"
include "bicomd.mm"
include "imbi2d.mm"
include "albidv.mm"
include "pm5.32i.mm"
include "wb.mm"
include "pm5.5.mm"
include "syl.mm"
include "anbi1d.mm"
include "elcnvcnvintab.mm"
include "vex.mm"
include "cnvexg.mm"
include "mp2b.mm"
include "wrel.mm"
include "wss.mm"
include "relcnv.mm"
include "df-rel.mm"
include "mpbi.mm"
include "elmapintrab.mm"
include "ax-mp.mm"
include "3bitr4g.mm"
include "eqrdv.mm"

theorem cnvcnvintabd
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vw: setvar w
  let vy: setvar y
  assume cnvcnvintabd.x: |- ( ph -> E. x ps )

  disjoint ps w
  disjoint w x
  disjoint ph y
  disjoint w y
  disjoint ps y
  disjoint x y
  assert |- ( ph -> `' `' |^| { x | ps } = |^| { w e. ~P ( _V X. _V ) | E. x ( w = `' `' x /\ ps ) } )

  proof
    wph
    vy
    wps
    vx
    cab
    cint
    ccnv
    ccnv
    #
    vw
    cv
    vx
    cv
    #
    ccnv
    #
    ccnv
    #
    wceq
    wps
    wa
    vx
    wex
    vw
    cvv
    cvv
    cxp
    #
    cpw
    crab
    cint
    #
    wph
    vy
    cv
    #
    @4
    wcel
    #
    wps
    vy
    vx
    wel
    #
    wi
    #
    vx
    wal
    #
    wa
    #
    wps
    vx
    wex
    #
    @7
    wi
    #
    wps
    @6
    @3
    wcel
    #
    wi
    #
    vx
    wal
    #
    wa
    #
    @6
    @0
    wcel
    @6
    @5
    wcel
    #
    @11
    @7
    @16
    wa
    wph
    @17
    @7
    @10
    @16
    @7
    @9
    @15
    vx
    @7
    @8
    @14
    wps
    @7
    @14
    @8
    @14
    @6
    @1
    @4
    cin
    #
    wcel
    #
    @7
    @8
    @3
    @19
    @6
    @1
    cnvcnv
    eleq2i
    @20
    @8
    @7
    @6
    @1
    @4
    elin
    rbaib
    syl5bb
    bicomd
    imbi2d
    albidv
    pm5.32i
    wph
    @7
    @13
    @16
    wph
    @13
    @7
    wph
    @12
    @13
    @7
    wb
    cnvcnvintabd.x
    @12
    @7
    pm5.5
    syl
    bicomd
    anbi1d
    syl5bb
    wps
    vx
    @6
    elcnvcnvintab
    @6
    cvv
    wcel
    @18
    @17
    wb
    vy
    vex
    wps
    vx
    vw
    @6
    @4
    @3
    cvv
    @1
    cvv
    wcel
    @2
    cvv
    wcel
    @3
    cvv
    wcel
    vx
    vex
    @1
    cvv
    cnvexg
    @2
    cvv
    cnvexg
    mp2b
    @3
    wrel
    @3
    @4
    wss
    @2
    relcnv
    @3
    df-rel
    mpbi
    elmapintrab
    ax-mp
    3bitr4g
    eqrdv
end
