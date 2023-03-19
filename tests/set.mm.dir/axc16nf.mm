include "weq.mm"
include "wal.mm"
include "wex.mm"
include "wn.mm"
include "df-ex.mm"
include "axc16g.mm"
include "con1d.mm"
include "syl5bi.mm"
include "syld.mm"
include "nfd.mm"

theorem axc16nf
  param wph: wff ph
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z

  disjoint x y
  assert |- ( A. x x = y -> F/ z ph )

  proof
    vx
    vy
    weq
    vx
    wal
    #
    wph
    vz
    @0
    wph
    vz
    wex
    #
    wph
    wph
    vz
    wal
    @1
    wph
    wn
    #
    vz
    wal
    #
    wn
    @0
    wph
    wph
    vz
    df-ex
    @0
    wph
    @3
    @2
    vx
    vy
    vz
    axc16g
    con1d
    syl5bi
    wph
    vx
    vy
    vz
    axc16g
    syld
    nfd
end
