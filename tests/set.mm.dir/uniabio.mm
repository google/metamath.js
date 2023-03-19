include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "wal.mm"
include "cab.mm"
include "cuni.mm"
include "csn.mm"
include "abbi.mm"
include "biimpi.mm"
include "df-sn.mm"
include "syl6eqr.mm"
include "unieqd.mm"
include "vex.mm"
include "unisn.mm"
include "syl6eq.mm"

theorem uniabio
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let wps: wff ps

  disjoint x y
  disjoint ph z
  disjoint ps z
  disjoint x z
  disjoint y z
  assert |- ( A. x ( ph <-> x = y ) -> U. { x | ph } = y )

  proof
    wph
    vx
    cv
    vy
    cv
    #
    wceq
    #
    wb
    vx
    wal
    #
    wph
    vx
    cab
    #
    cuni
    @0
    csn
    #
    cuni
    @0
    @2
    @3
    @4
    @2
    @3
    @1
    vx
    cab
    #
    @4
    @2
    @3
    @5
    wceq
    wph
    @1
    vx
    abbi
    biimpi
    vx
    @0
    df-sn
    syl6eqr
    unieqd
    @0
    vy
    vex
    unisn
    syl6eq
end
