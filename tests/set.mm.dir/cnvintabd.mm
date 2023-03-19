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
include "wi.mm"
include "wal.mm"
include "wb.mm"
include "pm5.5.mm"
include "syl.mm"
include "bicomd.mm"
include "anbi1d.mm"
include "elcnvintab.mm"
include "vex.mm"
include "cnvex.mm"
include "wrel.mm"
include "wss.mm"
include "relcnv.mm"
include "df-rel.mm"
include "mpbi.mm"
include "elmapintrab.mm"
include "ax-mp.mm"
include "3bitr4g.mm"
include "eqrdv.mm"

theorem cnvintabd
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vw: setvar w
  let vy: setvar y
  assume cnvintabd.x: |- ( ph -> E. x ps )

  disjoint ps w
  disjoint w x
  disjoint ph y
  disjoint w y
  disjoint ps y
  disjoint x y
  assert |- ( ph -> `' |^| { x | ps } = |^| { w e. ~P ( _V X. _V ) | E. x ( w = `' x /\ ps ) } )

  proof
    wph
    vy
    wps
    vx
    cab
    cint
    ccnv
    #
    vw
    cv
    vx
    cv
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
    @3
    wcel
    #
    wps
    @5
    @2
    wcel
    wi
    vx
    wal
    #
    wa
    wps
    vx
    wex
    #
    @6
    wi
    #
    @7
    wa
    #
    @5
    @0
    wcel
    @5
    @4
    wcel
    #
    wph
    @6
    @9
    @7
    wph
    @9
    @6
    wph
    @8
    @9
    @6
    wb
    cnvintabd.x
    @8
    @6
    pm5.5
    syl
    bicomd
    anbi1d
    wps
    vx
    @5
    elcnvintab
    @5
    cvv
    wcel
    @11
    @10
    wb
    vy
    vex
    wps
    vx
    vw
    @5
    @3
    @2
    cvv
    @1
    vx
    vex
    cnvex
    @2
    wrel
    @2
    @3
    wss
    @1
    relcnv
    @2
    df-rel
    mpbi
    elmapintrab
    ax-mp
    3bitr4g
    eqrdv
end
