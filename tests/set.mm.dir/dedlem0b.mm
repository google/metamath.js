include "wn.mm"
include "wi.mm"
include "wa.mm"
include "pm2.21.mm"
include "imim2d.mm"
include "com23.mm"
include "simpr.mm"
include "imim12i.mm"
include "con1d.mm"
include "com12.mm"
include "impbid.mm"

theorem dedlem0b
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( -. ph -> ( ps <-> ( ( ps -> ph ) -> ( ch /\ ph ) ) ) )

  proof
    wph
    wn
    #
    wps
    wps
    wph
    wi
    #
    wch
    wph
    wa
    #
    wi
    #
    @0
    @1
    wps
    @2
    @0
    wph
    @2
    wps
    wph
    @2
    pm2.21
    imim2d
    com23
    @3
    @0
    wps
    @3
    wps
    wph
    wps
    wn
    @1
    @2
    wph
    wps
    wph
    pm2.21
    wch
    wph
    simpr
    imim12i
    con1d
    com12
    impbid
end
