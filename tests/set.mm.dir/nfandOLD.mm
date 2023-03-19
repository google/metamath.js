include "wa.mm"
include "wn.mm"
include "wi.mm"
include "df-an.mm"
include "nfndOLD.mm"
include "nfimdOLD.mm"
include "nfxfrdOLD.mm"

theorem nfandOLD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume nfandOLD.1: |- ( ph -> nfOLD x ps )
  assume nfandOLD.2: |- ( ph -> nfOLD x ch )


  assert |- ( ph -> nfOLD x ( ps /\ ch ) )

  proof
    wps
    wch
    wa
    wps
    wch
    wn
    #
    wi
    #
    wn
    wph
    vx
    wps
    wch
    df-an
    wph
    @1
    vx
    wph
    wps
    @0
    vx
    nfandOLD.1
    wph
    wch
    vx
    nfandOLD.2
    nfndOLD
    nfimdOLD
    nfndOLD
    nfxfrdOLD
end
