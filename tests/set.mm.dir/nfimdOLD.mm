include "wnfOLD.mm"
include "wi.mm"
include "wal.mm"
include "nfnf1OLDOLD.mm"
include "nfrOLD.mm"
include "imim2d.mm"
include "19.21tOLD.mm"
include "biimprd.mm"
include "syl9r.mm"
include "alrimdOLD.mm"
include "df-nfOLD.mm"
include "syl6ibr.mm"
include "sylc.mm"

theorem nfimdOLD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume nfimdOLD.1: |- ( ph -> nfOLD x ps )
  assume nfimdOLD.2: |- ( ph -> nfOLD x ch )


  assert |- ( ph -> nfOLD x ( ps -> ch ) )

  proof
    wph
    wps
    vx
    wnfOLD
    #
    wch
    vx
    wnfOLD
    #
    wps
    wch
    wi
    #
    vx
    wnfOLD
    #
    nfimdOLD.1
    nfimdOLD.2
    @0
    @1
    @2
    @2
    vx
    wal
    #
    wi
    #
    vx
    wal
    @3
    @0
    @1
    @5
    vx
    wps
    vx
    nfnf1OLDOLD
    wch
    vx
    nfnf1OLDOLD
    @1
    @2
    wps
    wch
    vx
    wal
    #
    wi
    #
    @0
    @4
    @1
    wch
    @6
    wps
    wch
    vx
    nfrOLD
    imim2d
    @0
    @4
    @7
    wps
    wch
    vx
    19.21tOLD
    biimprd
    syl9r
    alrimdOLD
    @2
    vx
    df-nfOLD
    syl6ibr
    sylc
end
