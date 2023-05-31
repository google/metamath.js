include "weq.mm"
include "wal.mm"
include "wi.mm"
include "wnf.mm"
include "dral1.mm"
include "imbi12d.mm"
include "nf5.mm"
include "3bitr4g.mm"

theorem drnf1
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  param vy: setvar y
  assume dral1.1: |- ( A. x x = y -> ( ph <-> ps ) )


  assert |- ( A. x x = y -> ( F/ x ph <-> F/ y ps ) )

  proof
    vx
    vy
    weq
    vx
    wal
    #
    wph
    wph
    vx
    wal
    #
    wi
    #
    vx
    wal
    wps
    wps
    vy
    wal
    #
    wi
    #
    vy
    wal
    wph
    vx
    wnf
    wps
    vy
    wnf
    @2
    @4
    vx
    vy
    @0
    wph
    wps
    @1
    @3
    dral1.1
    wph
    wps
    vx
    vy
    dral1.1
    dral1
    imbi12d
    dral1
    wph
    vx
    nf5
    wps
    vy
    nf5
    3bitr4g
end
