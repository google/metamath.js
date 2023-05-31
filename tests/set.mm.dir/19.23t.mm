include "wnf.mm"
include "wn.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "wb.mm"
include "nfnt.mm"
include "19.21t.mm"
include "syl.mm"
include "con34b.mm"
include "albii.mm"
include "eximal.mm"
include "3bitr4g.mm"

theorem 19.23t
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x


  assert |- ( F/ x ps -> ( A. x ( ph -> ps ) <-> ( E. x ph -> ps ) ) )

  proof
    wps
    vx
    wnf
    #
    wps
    wn
    #
    wph
    wn
    #
    wi
    #
    vx
    wal
    #
    @1
    @2
    vx
    wal
    wi
    #
    wph
    wps
    wi
    #
    vx
    wal
    wph
    vx
    wex
    wps
    wi
    @0
    @1
    vx
    wnf
    @4
    @5
    wb
    wps
    vx
    nfnt
    @1
    @2
    vx
    19.21t
    syl
    @6
    @3
    vx
    wph
    wps
    con34b
    albii
    wph
    wps
    vx
    eximal
    3bitr4g
end
