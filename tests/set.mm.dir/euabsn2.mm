include "weu.mm"
include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wal.mm"
include "wex.mm"
include "cab.mm"
include "csn.mm"
include "df-eu.mm"
include "wcel.mm"
include "abeq1.mm"
include "velsn.mm"
include "bibi2i.mm"
include "albii.mm"
include "bitri.mm"
include "exbii.mm"
include "bitr4i.mm"

theorem euabsn2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint ph y
  disjoint A y
  assert |- ( E! x ph <-> E. y { x | ph } = { y } )

  proof
    wph
    vx
    weu
    wph
    vx
    cv
    #
    vy
    cv
    #
    wceq
    #
    wb
    #
    vx
    wal
    #
    vy
    wex
    wph
    vx
    cab
    @1
    csn
    #
    wceq
    #
    vy
    wex
    wph
    vx
    vy
    df-eu
    @6
    @4
    vy
    @6
    wph
    @0
    @5
    wcel
    #
    wb
    #
    vx
    wal
    @4
    wph
    vx
    @5
    abeq1
    @8
    @3
    vx
    @7
    @2
    wph
    vx
    @1
    velsn
    bibi2i
    albii
    bitri
    exbii
    bitr4i
end
