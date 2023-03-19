include "mpbii.mm"
include "exlimi.mm"

theorem bj-exlimmpbi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume bj-exlimmpbi.nf: |- F/ x ps
  assume bj-exlimmpbi.maj: |- ( ch -> ( ph <-> ps ) )
  assume bj-exlimmpbi.min: |- ph


  assert |- ( E. x ch -> ps )

  proof
    wch
    wps
    vx
    bj-exlimmpbi.nf
    wch
    wph
    wps
    bj-exlimmpbi.min
    bj-exlimmpbi.maj
    mpbii
    exlimi
end
