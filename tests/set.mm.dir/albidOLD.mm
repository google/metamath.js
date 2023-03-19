include "nfriOLD.mm"
include "albidh.mm"

theorem albidOLD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume albidOLD.1: |- nfOLD x ph
  assume albidOLD.2: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ( A. x ps <-> A. x ch ) )

  proof
    wph
    wps
    wch
    vx
    wph
    vx
    albidOLD.1
    nfriOLD
    albidOLD.2
    albidh
end
