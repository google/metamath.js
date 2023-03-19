include "wal.mm"
include "wex.mm"
include "19.12.mm"
include "nfrd.mm"
include "alimd.mm"
include "ax-11.mm"
include "syl56.mm"
include "nfd.mm"

theorem nfald
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume nfald.1: |- F/ y ph
  assume nfald.2: |- ( ph -> F/ x ps )


  assert |- ( ph -> F/ x A. y ps )

  proof
    wph
    wps
    vy
    wal
    #
    vx
    @0
    vx
    wex
    wps
    vx
    wex
    #
    vy
    wal
    wph
    wps
    vx
    wal
    #
    vy
    wal
    @0
    vx
    wal
    wps
    vx
    vy
    19.12
    wph
    @1
    @2
    vy
    nfald.1
    wph
    wps
    vx
    nfald.2
    nfrd
    alimd
    wps
    vy
    vx
    ax-11
    syl56
    nfd
end
