include "wn.mm"
include "wex.mm"
include "wal.mm"
include "wa.mm"
include "wi.mm"
include "exanali.mm"
include "mpbir.mm"
include "alex.mm"
include "biimpri.mm"
include "19.21bi.mm"
include "simpl.mm"
include "a1i.mm"
include "19.8a.mm"
include "syl6an.mm"
include "notnot.mm"
include "syl6.mm"
include "con3.mm"
include "mpsylsyld.mm"
include "hbe1.mm"
include "hbn.mm"
include "hbn1.mm"
include "eexinst01.mm"
include "exnal.mm"
include "sylibr.mm"
include "wo.mm"
include "pm3.13.mm"
include "ax-mp.mm"
include "simpr.mm"
include "syl.mm"
include "pm2.53.mm"
include "mpsyl.mm"
include "con5i.mm"
include "con3d.mm"
include "eexinst11.mm"
include "sylib.mm"

theorem vk15.4j
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  assume vk15.4j.1: |- -. ( E. x -. ph /\ E. x ( ps /\ -. ch ) )
  assume vk15.4j.2: |- ( A. x ch -> -. E. x ( th /\ ta ) )
  assume vk15.4j.3: |- -. A. x ( ta -> ph )


  assert |- ( -. E. x -. th -> -. A. x ps )

  proof
    wth
    wn
    #
    vx
    wex
    #
    wn
    #
    wps
    wn
    #
    vx
    wex
    #
    wps
    vx
    wal
    wn
    @2
    wch
    wn
    #
    @4
    vx
    @2
    wch
    vx
    wal
    #
    wn
    #
    @5
    vx
    wex
    @2
    wta
    wph
    wn
    #
    wa
    #
    @7
    vx
    @9
    vx
    wex
    wta
    wph
    wi
    vx
    wal
    wn
    vk15.4j.3
    wta
    wph
    vx
    exanali
    mpbir
    #
    @6
    wth
    wta
    wa
    #
    vx
    wex
    #
    wn
    #
    wi
    @2
    @9
    @13
    wn
    #
    @7
    vk15.4j.2
    @2
    @9
    @12
    @14
    @2
    wth
    @9
    wta
    @12
    @2
    wth
    vx
    wth
    vx
    wal
    @2
    wth
    vx
    alex
    biimpri
    19.21bi
    @9
    wta
    wi
    @2
    wta
    @8
    simpl
    a1i
    @11
    vx
    19.8a
    syl6an
    @12
    notnot
    syl6
    @6
    @13
    con3
    mpsylsyld
    @1
    vx
    @0
    vx
    hbe1
    hbn
    #
    wch
    vx
    hbn1
    eexinst01
    wch
    vx
    exnal
    sylibr
    @2
    @5
    @3
    @4
    @2
    wps
    wch
    @2
    wps
    wch
    wi
    #
    vx
    @2
    wps
    @5
    wa
    vx
    wex
    #
    wn
    #
    @16
    vx
    wal
    #
    @8
    vx
    wex
    #
    wn
    #
    @18
    wo
    #
    @2
    @21
    wn
    #
    @18
    @20
    @17
    wa
    wn
    @22
    vk15.4j.1
    @20
    @17
    pm3.13
    ax-mp
    @2
    @20
    @23
    @2
    @9
    @20
    vx
    @10
    @2
    @9
    @8
    @20
    @9
    @8
    wi
    @2
    wta
    @8
    simpr
    a1i
    @8
    vx
    19.8a
    syl6
    @15
    @8
    vx
    hbe1
    eexinst01
    @20
    notnot
    syl
    @21
    @18
    pm2.53
    mpsyl
    @17
    @19
    wps
    wch
    vx
    exanali
    con5i
    syl
    19.21bi
    con3d
    @3
    vx
    19.8a
    syl6
    @15
    @3
    vx
    hbe1
    eexinst11
    wps
    vx
    exnal
    sylib
end
