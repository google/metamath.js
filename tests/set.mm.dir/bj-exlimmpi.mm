include "mpi.mm"
include "exlimi.mm"

theorem bj-exlimmpi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume bj-exlimmpi.nf: |- F/ x ps
  assume bj-exlimmpi.maj: |- ( ch -> ( ph -> ps ) )
  assume bj-exlimmpi.min: |- ph


  assert |- ( E. x ch -> ps )

  proof
    wch
    wps
    vx
    bj-exlimmpi.nf
    wch
    wph
    wps
    bj-exlimmpi.min
    bj-exlimmpi.maj
    mpi
    exlimi
end
