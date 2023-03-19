include "weq.mm"
include "wb.mm"
include "wal.mm"
include "wex.mm"
include "wsbc.mm"
include "weu.mm"
include "sbcex2.mm"
include "sbcal.mm"
include "exbii.mm"
include "cvv.mm"
include "wcel.mm"
include "sbcbig.mm"
include "ax-mp.mm"
include "sbcg.mm"
include "bibi2i.mm"
include "bitri.mm"
include "albii.mm"
include "3bitri.mm"
include "df-eu.mm"
include "sbcbii.mm"
include "3bitr4i.mm"

theorem bnj89
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cZ: class Z
  let vw: setvar w
  assume bnj89.1: |- Z e. _V

  disjoint Z x
  disjoint x y
  disjoint Z w
  disjoint w x
  disjoint ph w
  disjoint w y
  assert |- ( [. Z / y ]. E! x ph <-> E! x [. Z / y ]. ph )

  proof
    wph
    vx
    vw
    weq
    #
    wb
    #
    vx
    wal
    #
    vw
    wex
    #
    vy
    cZ
    wsbc
    #
    wph
    vy
    cZ
    wsbc
    #
    @0
    wb
    #
    vx
    wal
    #
    vw
    wex
    #
    wph
    vx
    weu
    #
    vy
    cZ
    wsbc
    @5
    vx
    weu
    @4
    @2
    vy
    cZ
    wsbc
    #
    vw
    wex
    @1
    vy
    cZ
    wsbc
    #
    vx
    wal
    #
    vw
    wex
    @8
    @2
    vw
    vy
    cZ
    sbcex2
    @10
    @12
    vw
    @1
    vx
    vy
    cZ
    sbcal
    exbii
    @12
    @7
    vw
    @11
    @6
    vx
    @11
    @5
    @0
    vy
    cZ
    wsbc
    #
    wb
    #
    @6
    cZ
    cvv
    wcel
    #
    @11
    @14
    wb
    bnj89.1
    wph
    @0
    vy
    cZ
    cvv
    sbcbig
    ax-mp
    @13
    @0
    @5
    @15
    @13
    @0
    wb
    bnj89.1
    @0
    vy
    cZ
    cvv
    sbcg
    ax-mp
    bibi2i
    bitri
    albii
    exbii
    3bitri
    @9
    @3
    vy
    cZ
    wph
    vx
    vw
    df-eu
    sbcbii
    @5
    vx
    vw
    df-eu
    3bitr4i
end
