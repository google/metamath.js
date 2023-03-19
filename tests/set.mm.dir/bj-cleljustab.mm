include "cv.mm"
include "cab.mm"
include "wcel.mm"
include "wsb.mm"
include "weq.mm"
include "wa.mm"
include "wex.mm"
include "df-clab.mm"
include "ax6ev.mm"
include "biantrur.mm"
include "19.41v.mm"
include "bicomi.mm"
include "wb.mm"
include "sbequ.mm"
include "equcoms.mm"
include "pm5.32i.mm"
include "exbii.mm"
include "3bitri.mm"
include "anbi2i.mm"

theorem bj-cleljustab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x z
  disjoint y z
  disjoint ph z
  assert |- ( x e. { y | ph } <-> E. z ( z = x /\ z e. { y | ph } ) )

  proof
    vx
    cv
    wph
    vy
    cab
    #
    wcel
    wph
    vy
    vx
    wsb
    #
    vz
    vx
    weq
    #
    wph
    vy
    vz
    wsb
    #
    wa
    #
    vz
    wex
    #
    @2
    vz
    cv
    @0
    wcel
    #
    wa
    #
    vz
    wex
    wph
    vx
    vy
    df-clab
    @1
    @2
    vz
    wex
    #
    @1
    wa
    #
    @2
    @1
    wa
    #
    vz
    wex
    #
    @5
    @8
    @1
    vz
    vx
    ax6ev
    biantrur
    @11
    @9
    @2
    @1
    vz
    19.41v
    bicomi
    @10
    @4
    vz
    @2
    @1
    @3
    @1
    @3
    wb
    vx
    vz
    wph
    vx
    vz
    vy
    sbequ
    equcoms
    pm5.32i
    exbii
    3bitri
    @4
    @7
    vz
    @3
    @6
    @2
    @6
    @3
    wph
    vz
    vy
    df-clab
    bicomi
    anbi2i
    exbii
    3bitri
end
