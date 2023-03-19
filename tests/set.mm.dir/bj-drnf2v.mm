include "weq.mm"
include "wal.mm"
include "nfv.mm"
include "nfbidf.mm"

theorem bj-drnf2v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume bj-drnf2v.1: |- ( A. x x = y -> ( ph <-> ps ) )

  disjoint x y
  disjoint x z
  disjoint y z
  assert |- ( A. x x = y -> ( F/ z ph <-> F/ z ps ) )

  proof
    vx
    vy
    weq
    vx
    wal
    #
    wph
    wps
    vz
    @0
    vz
    nfv
    bj-drnf2v.1
    nfbidf
end
