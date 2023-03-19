include "wi.mm"
include "wex.mm"
include "wal.mm"
include "19.35.mm"
include "wn.mm"
include "wnf.mm"
include "nf4.mm"
include "sylib.mm"
include "pm2.21.mm"
include "alimi.mm"
include "syl6.mm"
include "nfrd.mm"
include "ala1.mm"
include "jad.mm"
include "syl5bi.mm"
include "nfd.mm"

theorem nfimdOLDOLD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume nfimd.1: |- ( ph -> F/ x ps )
  assume nfimd.2: |- ( ph -> F/ x ch )


  assert |- ( ph -> F/ x ( ps -> ch ) )

  proof
    wph
    wps
    wch
    wi
    #
    vx
    @0
    vx
    wex
    wps
    vx
    wal
    #
    wch
    vx
    wex
    #
    wi
    wph
    @0
    vx
    wal
    #
    wps
    wch
    vx
    19.35
    wph
    @1
    @2
    @3
    wph
    @1
    wn
    #
    wps
    wn
    #
    vx
    wal
    #
    @3
    wph
    wps
    vx
    wnf
    @4
    @6
    wi
    nfimd.1
    wps
    vx
    nf4
    sylib
    @5
    @0
    vx
    wps
    wch
    pm2.21
    alimi
    syl6
    wph
    @2
    wch
    vx
    wal
    @3
    wph
    wch
    vx
    nfimd.2
    nfrd
    wch
    wps
    vx
    ala1
    syl6
    jad
    syl5bi
    nfd
end
