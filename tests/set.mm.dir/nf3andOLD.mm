include "w3a.mm"
include "wa.mm"
include "df-3an.mm"
include "nfandOLD.mm"
include "nfxfrdOLD.mm"

theorem nf3andOLD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  assume nfandOLD.1: |- ( ph -> nfOLD x ps )
  assume nfandOLD.2: |- ( ph -> nfOLD x ch )
  assume nfand.3OLD: |- ( ph -> nfOLD x th )


  assert |- ( ph -> nfOLD x ( ps /\ ch /\ th ) )

  proof
    wps
    wch
    wth
    w3a
    wps
    wch
    wa
    #
    wth
    wa
    wph
    vx
    wps
    wch
    wth
    df-3an
    wph
    @0
    wth
    vx
    wph
    wps
    wch
    vx
    nfandOLD.1
    nfandOLD.2
    nfandOLD
    nfand.3OLD
    nfandOLD
    nfxfrdOLD
end
