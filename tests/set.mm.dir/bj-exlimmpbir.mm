include "mpbiri.mm"
include "exlimi.mm"

theorem bj-exlimmpbir
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume bj-exlimmpbir.nf: |- F/ x ph
  assume bj-exlimmpbir.maj: |- ( ch -> ( ph <-> ps ) )
  assume bj-exlimmpbir.min: |- ps


  assert |- ( E. x ch -> ph )

  proof
    wch
    wph
    vx
    bj-exlimmpbir.nf
    wch
    wph
    wps
    bj-exlimmpbir.min
    bj-exlimmpbir.maj
    mpbiri
    exlimi
end
