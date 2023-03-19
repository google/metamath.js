include "wal.mm"
include "nfal.mm"
include "spimv1.mm"
include "alrimi.mm"

theorem cbv3v
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  param vy: setvar y
  assume cbv3v.nf1: |- F/ y ph
  assume cbv3v.nf2: |- F/ x ps
  assume cbv3v.1: |- ( x = y -> ( ph -> ps ) )

  disjoint x y
  assert |- ( A. x ph -> A. y ps )

  proof
    wph
    vx
    wal
    wps
    vy
    wph
    vy
    vx
    cbv3v.nf1
    nfal
    wph
    wps
    vx
    vy
    cbv3v.nf2
    cbv3v.1
    spimv1
    alrimi
end
