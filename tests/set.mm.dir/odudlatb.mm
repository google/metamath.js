include "wcel.mm"
include "clat.mm"
include "cv.mm"
include "cjn.mm"
include "cfv.mm"
include "co.mm"
include "cmee.mm"
include "wceq.mm"
include "cbs.mm"
include "wral.mm"
include "wa.mm"
include "cdlat.mm"
include "eqid.mm"
include "latdisd.mm"
include "bicomd.mm"
include "pm5.32i.mm"
include "odulatb.mm"
include "anbi1d.mm"
include "syl5bb.mm"
include "isdlat.mm"
include "odubas.mm"
include "odujoin.mm"
include "odumeet.mm"
include "3bitr4g.mm"

theorem odudlatb
  let cD: class D
  let cK: class K
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume odudlat.d: |- D = ( ODual ` K )


  assert |- ( K e. V -> ( K e. DLat <-> D e. DLat ) )

  proof
    cK
    cV
    wcel
    #
    cK
    clat
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    vz
    cv
    #
    cK
    cjn
    cfv
    #
    co
    cK
    cmee
    cfv
    #
    co
    @2
    @3
    @6
    co
    @2
    @4
    @6
    co
    @5
    co
    wceq
    vz
    cK
    cbs
    cfv
    #
    wral
    vy
    @7
    wral
    vx
    @7
    wral
    #
    wa
    #
    cD
    clat
    wcel
    #
    @2
    @3
    @4
    @6
    co
    @5
    co
    @2
    @3
    @5
    co
    @2
    @4
    @5
    co
    @6
    co
    wceq
    vz
    @7
    wral
    vy
    @7
    wral
    vx
    @7
    wral
    #
    wa
    #
    cK
    cdlat
    wcel
    cD
    cdlat
    wcel
    @9
    @1
    @11
    wa
    @0
    @12
    @1
    @8
    @11
    @1
    @11
    @8
    vx
    vy
    vz
    @7
    @5
    cK
    @6
    @7
    eqid
    #
    @5
    eqid
    #
    @6
    eqid
    #
    latdisd
    bicomd
    pm5.32i
    @0
    @1
    @10
    @11
    cD
    cK
    cV
    odudlat.d
    odulatb
    anbi1d
    syl5bb
    vx
    vy
    vz
    @7
    @5
    cK
    @6
    @13
    @14
    @15
    isdlat
    vx
    vy
    vz
    @7
    @6
    cD
    @5
    @7
    cD
    cK
    odudlat.d
    @13
    odubas
    cD
    @6
    cK
    odudlat.d
    @15
    odujoin
    cD
    @5
    cK
    odudlat.d
    @14
    odumeet
    isdlat
    3bitr4g
end
