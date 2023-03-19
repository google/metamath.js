include "wal.mm"
include "alimi.mm"
include "alcomiw.mm"
include "syl.mm"

theorem hbalw
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume hbalw.1: |- ( x = z -> ( ph <-> ps ) )
  assume hbalw.2: |- ( ph -> A. x ph )

  disjoint x z
  disjoint x y
  disjoint ph z
  disjoint ps x
  assert |- ( A. y ph -> A. x A. y ph )

  proof
    wph
    vy
    wal
    #
    wph
    vx
    wal
    #
    vy
    wal
    @0
    vx
    wal
    wph
    @1
    vy
    hbalw.2
    alimi
    wph
    wps
    vy
    vx
    vz
    hbalw.1
    alcomiw
    syl
end
