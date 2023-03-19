include "wn.mm"
include "wi.mm"
include "wal.mm"
include "wo.mm"
include "bi2.04.mm"
include "albii.mm"
include "19.21v.mm"
include "bitri.mm"
include "df-or.mm"
include "imbi2i.mm"
include "3bitr4i.mm"

theorem pm10.541
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x

  disjoint ch x
  assert |- ( A. x ( ph -> ( ch \/ ps ) ) <-> ( ch \/ A. x ( ph -> ps ) ) )

  proof
    wph
    wch
    wn
    #
    wps
    wi
    #
    wi
    #
    vx
    wal
    #
    @0
    wph
    wps
    wi
    #
    vx
    wal
    #
    wi
    #
    wph
    wch
    wps
    wo
    #
    wi
    #
    vx
    wal
    wch
    @5
    wo
    @3
    @0
    @4
    wi
    #
    vx
    wal
    @6
    @2
    @9
    vx
    wph
    @0
    wps
    bi2.04
    albii
    @0
    @4
    vx
    19.21v
    bitri
    @8
    @2
    vx
    @7
    @1
    wph
    wch
    wps
    df-or
    imbi2i
    albii
    wch
    @5
    df-or
    3bitr4i
end
