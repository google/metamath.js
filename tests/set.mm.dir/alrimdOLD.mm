include "wnfOLD.mm"
include "a1i.mm"
include "alrimddOLD.mm"

theorem alrimdOLD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume alrimdOLD.1: |- nfOLD x ph
  assume alrimdOLD.2: |- nfOLD x ps
  assume alrimdOLD.3: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( ps -> A. x ch ) )

  proof
    wph
    wps
    wch
    vx
    alrimdOLD.1
    wps
    vx
    wnfOLD
    wph
    alrimdOLD.2
    a1i
    alrimdOLD.3
    alrimddOLD
end
