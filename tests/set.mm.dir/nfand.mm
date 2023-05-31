include "wa.mm"
include "wn.mm"
include "wi.mm"
include "df-an.mm"
include "nfnd.mm"
include "nfimd.mm"
include "nfxfrd.mm"

theorem nfand
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param vx: setvar x
  assume nfand.1: |- ( ph -> F/ x ps )
  assume nfand.2: |- ( ph -> F/ x ch )


  assert |- ( ph -> F/ x ( ps /\ ch ) )

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
    nfand.1
    wph
    wch
    vx
    nfand.2
    nfnd
    nfimd
    nfnd
    nfxfrd
end
