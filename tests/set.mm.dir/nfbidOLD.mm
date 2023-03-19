include "wb.mm"
include "wi.mm"
include "wa.mm"
include "dfbi2.mm"
include "nfimdOLD.mm"
include "nfandOLD.mm"
include "nfxfrdOLD.mm"

theorem nfbidOLD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume nfbidOLD.1: |- ( ph -> nfOLD x ps )
  assume nfbidOLD.2: |- ( ph -> nfOLD x ch )


  assert |- ( ph -> nfOLD x ( ps <-> ch ) )

  proof
    wps
    wch
    wb
    wps
    wch
    wi
    #
    wch
    wps
    wi
    #
    wa
    wph
    vx
    wps
    wch
    dfbi2
    wph
    @0
    @1
    vx
    wph
    wps
    wch
    vx
    nfbidOLD.1
    nfbidOLD.2
    nfimdOLD
    wph
    wch
    wps
    vx
    nfbidOLD.2
    nfbidOLD.1
    nfimdOLD
    nfandOLD
    nfxfrdOLD
end
