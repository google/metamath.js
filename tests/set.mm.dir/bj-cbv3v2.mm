include "wal.mm"
include "nfv.mm"
include "spimv1.mm"
include "alrimi.mm"

theorem bj-cbv3v2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume bj-cbv3v2.nf: |- F/ x ps
  assume bj-cbv3v2.1: |- ( x = y -> ( ph -> ps ) )

  disjoint x y
  disjoint ph y
  assert |- ( A. x ph -> A. y ps )

  proof
    wph
    vx
    wal
    #
    wps
    vy
    @0
    vy
    nfv
    wph
    wps
    vx
    vy
    bj-cbv3v2.nf
    bj-cbv3v2.1
    spimv1
    alrimi
end
