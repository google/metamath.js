include "w3a.mm"
include "wa.mm"
include "df-3an.mm"
include "nfand.mm"
include "nfxfrd.mm"

theorem nf3and
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  assume nfand.1: |- ( ph -> F/ x ps )
  assume nfand.2: |- ( ph -> F/ x ch )
  assume nfand.3: |- ( ph -> F/ x th )


  assert |- ( ph -> F/ x ( ps /\ ch /\ th ) )

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
    nfand.1
    nfand.2
    nfand
    nfand.3
    nfand
    nfxfrd
end
