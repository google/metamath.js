include "weu.mm"
include "weq.mm"
include "wb.mm"
include "wal.mm"
include "wex.mm"
include "df-eu.mm"
include "nfv.mm"
include "wn.mm"
include "wa.mm"
include "wnf.mm"
include "nfeqf1.mm"
include "adantl.mm"
include "nfbid.mm"
include "nfald2.mm"
include "nfexd.mm"
include "nfxfrd.mm"

theorem nfeud2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume nfeud2.1: |- F/ y ph
  assume nfeud2.2: |- ( ( ph /\ -. A. x x = y ) -> F/ x ps )


  assert |- ( ph -> F/ x E! y ps )

  proof
    wps
    vy
    weu
    wps
    vy
    vz
    weq
    #
    wb
    #
    vy
    wal
    #
    vz
    wex
    wph
    vx
    wps
    vy
    vz
    df-eu
    wph
    @2
    vx
    vz
    wph
    vz
    nfv
    wph
    @1
    vx
    vy
    nfeud2.1
    wph
    vx
    vy
    weq
    vx
    wal
    wn
    #
    wa
    wps
    @0
    vx
    nfeud2.2
    @3
    @0
    vx
    wnf
    wph
    vx
    vy
    vz
    nfeqf1
    adantl
    nfbid
    nfald2
    nfexd
    nfxfrd
end
