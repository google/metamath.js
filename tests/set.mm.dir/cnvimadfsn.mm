include "ccnv.mm"
include "cvv.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "cv.mm"
include "wcel.mm"
include "cop.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "wbr.mm"
include "wne.mm"
include "dfima3.mm"
include "wb.mm"
include "vex.mm"
include "eldifvsn.mm"
include "ax-mp.mm"
include "opelcnv.mm"
include "df-br.mm"
include "bitr4i.mm"
include "anbi12ci.mm"
include "exbii.mm"
include "abbii.mm"
include "eqtri.mm"

theorem cnvimadfsn
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let cZ: class Z

  disjoint R x
  disjoint R y
  disjoint x y
  disjoint Z x
  disjoint Z y
  assert |- ( `' R " ( _V \ { Z } ) ) = { x | E. y ( x R y /\ y =/= Z ) }

  proof
    cR
    ccnv
    #
    cvv
    cZ
    csn
    cdif
    #
    cima
    vy
    cv
    #
    @1
    wcel
    #
    @2
    vx
    cv
    #
    cop
    @0
    wcel
    #
    wa
    #
    vy
    wex
    #
    vx
    cab
    @4
    @2
    cR
    wbr
    #
    @2
    cZ
    wne
    #
    wa
    #
    vy
    wex
    #
    vx
    cab
    vy
    vx
    @0
    @1
    dfima3
    @7
    @11
    vx
    @6
    @10
    vy
    @3
    @9
    @5
    @8
    @2
    cvv
    wcel
    @3
    @9
    wb
    vy
    vex
    #
    @2
    cZ
    cvv
    eldifvsn
    ax-mp
    @5
    @4
    @2
    cop
    cR
    wcel
    @8
    @2
    @4
    cR
    @12
    vx
    vex
    opelcnv
    @4
    @2
    cR
    df-br
    bitr4i
    anbi12ci
    exbii
    abbii
    eqtri
end
