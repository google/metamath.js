include "weq.mm"
include "wal.mm"
include "wi.mm"
include "wnf.mm"
include "bj-dral1v.mm"
include "imbi12d.mm"
include "nf5.mm"
include "3bitr4g.mm"

theorem bj-drnf1v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume bj-drnf1v.1: |- ( A. x x = y -> ( ph <-> ps ) )

  disjoint x y
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
    bj-drnf1v.1
    wph
    wps
    vx
    vy
    bj-drnf1v.1
    bj-dral1v
    imbi12d
    bj-dral1v
    wph
    vx
    nf5
    wps
    vy
    nf5
    3bitr4g
end
