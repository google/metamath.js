include "weq.mm"
include "wal.mm"
include "cab.mm"
include "wnfc.mm"
include "wn.mm"
include "wa.mm"
include "nfv.mm"
include "cv.mm"
include "wcel.mm"
include "wsb.mm"
include "df-clab.mm"
include "nfnae.mm"
include "nfan.mm"
include "nfsbd.mm"
include "nfxfrd.mm"
include "nfcd.mm"
include "ex.mm"
include "nfab1.mm"
include "eqidd.mm"
include "drnfc1.mm"
include "mpbiri.mm"
include "pm2.61d2.mm"

theorem nfabd2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume nfabd2.1: |- F/ y ph
  assume nfabd2.2: |- ( ( ph /\ -. A. x x = y ) -> F/ x ps )


  assert |- ( ph -> F/_ x { y | ps } )

  proof
    wph
    vx
    vy
    weq
    vx
    wal
    #
    vx
    wps
    vy
    cab
    #
    wnfc
    #
    wph
    @0
    wn
    #
    @2
    wph
    @3
    wa
    #
    vx
    vz
    @1
    @4
    vz
    nfv
    vz
    cv
    @1
    wcel
    wps
    vy
    vz
    wsb
    @4
    vx
    wps
    vz
    vy
    df-clab
    @4
    wps
    vy
    vz
    vx
    wph
    @3
    vy
    nfabd2.1
    vx
    vy
    vy
    nfnae
    nfan
    nfabd2.2
    nfsbd
    nfxfrd
    nfcd
    ex
    @0
    @2
    vy
    @1
    wnfc
    wps
    vy
    nfab1
    vx
    vy
    @1
    @1
    @0
    @1
    eqidd
    drnfc1
    mpbiri
    pm2.61d2
end
