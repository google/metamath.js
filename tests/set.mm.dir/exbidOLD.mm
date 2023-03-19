include "nfriOLD.mm"
include "exbidh.mm"

theorem exbidOLD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume exbidOLD.1: |- nfOLD x ph
  assume exbidOLD.2: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ( E. x ps <-> E. x ch ) )

  proof
    wph
    wps
    wch
    vx
    wph
    vx
    exbidOLD.1
    nfriOLD
    exbidOLD.2
    exbidh
end
