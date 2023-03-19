include "wn.mm"
include "wo.mm"
include "wi.mm"
include "orc.mm"
include "olc.mm"
include "ja.mm"
include "imim1i.mm"
include "pm2.24.mm"
include "idd.mm"
include "jaod.mm"
include "com12.mm"
include "pm1.5.mm"
include "pm2.3.mm"
include "pm2.21.mm"
include "mth8.mm"
include "imim12i.mm"
include "pm2.43d.mm"
include "con4d.mm"
include "imor.mm"
include "3imtr3i.mm"
include "orim2i.mm"
include "4syl.mm"
include "3syl.mm"
include "3imtr4i.mm"
include "syl2im.mm"
include "imori.mm"

theorem meran1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( -. ( -. ( -. ph \/ ps ) \/ ( ch \/ ( th \/ ta ) ) ) \/ ( -. ( -. th \/ ph ) \/ ( ch \/ ( ta \/ ph ) ) ) )

  proof
    wph
    wn
    #
    wps
    wo
    #
    wn
    wch
    wth
    wta
    wo
    #
    wo
    #
    wo
    #
    wth
    wn
    #
    wph
    wo
    #
    wn
    wch
    wta
    wph
    wo
    #
    wo
    #
    wo
    #
    @1
    @3
    wi
    #
    @6
    @8
    wi
    @4
    @9
    @10
    wph
    wps
    wi
    #
    @3
    wi
    #
    @6
    wth
    wph
    wi
    #
    @8
    @11
    @1
    @3
    wph
    wps
    @1
    @0
    wps
    orc
    wps
    @0
    olc
    ja
    imim1i
    wth
    @6
    wph
    wth
    @5
    wph
    wph
    wth
    wph
    pm2.24
    wth
    wph
    idd
    jaod
    com12
    @11
    wn
    #
    @3
    wo
    #
    @13
    wn
    #
    @8
    wo
    #
    @12
    @13
    @8
    wi
    @15
    wch
    @14
    @2
    wo
    #
    wo
    wch
    @16
    @7
    wo
    #
    wo
    @17
    @14
    wch
    @2
    pm1.5
    @18
    @19
    wch
    @18
    @14
    wta
    wth
    wo
    wo
    wta
    @14
    wth
    wo
    #
    wo
    wta
    @16
    wph
    wo
    #
    wo
    @19
    @14
    wth
    wta
    pm2.3
    @14
    wta
    wth
    pm1.5
    @20
    @21
    wta
    @11
    wth
    wi
    #
    @13
    wph
    wi
    @20
    @21
    @22
    wph
    @13
    @22
    @0
    @16
    @0
    @11
    wth
    @0
    @16
    wi
    wph
    wps
    pm2.21
    wth
    wph
    mth8
    imim12i
    pm2.43d
    con4d
    @11
    wth
    imor
    @13
    wph
    imor
    3imtr3i
    orim2i
    wta
    @16
    wph
    pm1.5
    4syl
    orim2i
    wch
    @16
    @7
    pm1.5
    3syl
    @11
    @3
    imor
    @13
    @8
    imor
    3imtr4i
    syl2im
    @1
    @3
    imor
    @6
    @8
    imor
    3imtr3i
    imori
end
