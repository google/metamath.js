include "wn.mm"
include "wex.mm"
include "wal.mm"
include "wa.mm"
include "wi.mm"
include "exanali.mm"
include "biimpri.mm"
include "e0a.mm"
include "idn1.mm"
include "alex.mm"
include "e1a.mm"
include "sp.mm"
include "idn2.mm"
include "simpl.mm"
include "e2.mm"
include "pm3.2.mm"
include "e12.mm"
include "19.8a.mm"
include "notnot.mm"
include "con3.mm"
include "e02.mm"
include "hbe1.mm"
include "hbn.mm"
include "hba1.mm"
include "exinst01.mm"
include "exnal.mm"
include "wo.mm"
include "pm3.13.mm"
include "simpr.mm"
include "pm2.53.mm"
include "e01.mm"
include "con5i.mm"
include "com12.mm"
include "e21.mm"
include "exinst11.mm"
include "biimpi.mm"
include "in1.mm"

theorem vk15.4jVD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  assume vk15.4jVD.1: |- -. ( E. x -. ph /\ E. x ( ps /\ -. ch ) )
  assume vk15.4jVD.2: |- ( A. x ch -> -. E. x ( th /\ ta ) )
  assume vk15.4jVD.3: |- -. A. x ( ta -> ph )


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
    vx
    wal
    wn
    #
    @2
    wps
    wn
    #
    vx
    wex
    #
    @3
    @2
    wch
    wn
    #
    @5
    vx
    @2
    wch
    vx
    wal
    #
    wn
    #
    @6
    vx
    wex
    #
    @2
    wta
    wph
    wn
    #
    wa
    #
    @8
    vx
    wta
    wph
    wi
    vx
    wal
    wn
    #
    @11
    vx
    wex
    #
    vk15.4jVD.3
    @13
    @12
    wta
    wph
    vx
    exanali
    biimpri
    e0a
    #
    @7
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
    @11
    @17
    wn
    #
    @8
    vk15.4jVD.2
    @2
    @11
    @16
    @18
    @2
    @11
    @15
    @16
    @2
    wth
    @11
    wta
    @15
    @2
    wth
    vx
    wal
    #
    wth
    @2
    @2
    @19
    @2
    idn1
    @19
    @2
    wth
    vx
    alex
    biimpri
    e1a
    wth
    vx
    sp
    e1a
    @2
    @11
    @11
    wta
    @2
    @11
    idn2
    #
    wta
    @10
    simpl
    e2
    wth
    wta
    pm3.2
    e12
    @15
    vx
    19.8a
    e2
    @16
    notnot
    e2
    @7
    @17
    con3
    e02
    @1
    vx
    @0
    vx
    hbe1
    hbn
    #
    @7
    vx
    wch
    vx
    hba1
    hbn
    exinst01
    @9
    @8
    wch
    vx
    exnal
    biimpri
    e1a
    @2
    @6
    @4
    @5
    @2
    @6
    @6
    wps
    wch
    wi
    #
    @4
    @2
    @6
    idn2
    @2
    @22
    vx
    wal
    #
    @22
    @2
    wps
    @6
    wa
    vx
    wex
    #
    wn
    #
    @23
    @10
    vx
    wex
    #
    wn
    #
    @25
    wo
    #
    @2
    @27
    wn
    #
    @25
    @26
    @24
    wa
    wn
    @28
    vk15.4jVD.1
    @26
    @24
    pm3.13
    e0a
    @2
    @26
    @29
    @2
    @11
    @26
    vx
    @14
    @2
    @11
    @10
    @26
    @2
    @11
    @11
    @10
    @20
    wta
    @10
    simpr
    e2
    @10
    vx
    19.8a
    e2
    @21
    @10
    vx
    hbe1
    exinst01
    @26
    notnot
    e1a
    @27
    @25
    pm2.53
    e01
    @24
    @23
    wps
    wch
    vx
    exanali
    con5i
    e1a
    @22
    vx
    sp
    e1a
    @22
    @6
    @4
    wps
    wch
    con3
    com12
    e21
    @4
    vx
    19.8a
    e2
    @21
    @4
    vx
    hbe1
    exinst11
    @5
    @3
    wps
    vx
    exnal
    biimpi
    e1a
    in1
end
