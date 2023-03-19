include "wcad.mm"
include "wa.mm"
include "wxo.mm"
include "wo.mm"
include "wn.mm"
include "df-cad.mm"
include "idd.mm"
include "pm2.21.mm"
include "adantrd.mm"
include "jaod.mm"
include "orc.mm"
include "impbid1.mm"
include "syl5bb.mm"

theorem cad0
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( -. ch -> ( cadd ( ph , ps , ch ) <-> ( ph /\ ps ) ) )

  proof
    wph
    wps
    wch
    wcad
    wph
    wps
    wa
    #
    wch
    wph
    wps
    wxo
    #
    wa
    #
    wo
    #
    wch
    wn
    #
    @0
    wph
    wps
    wch
    df-cad
    @4
    @3
    @0
    @4
    @0
    @0
    @2
    @4
    @0
    idd
    @4
    wch
    @0
    @1
    wch
    @0
    pm2.21
    adantrd
    jaod
    @0
    @2
    orc
    impbid1
    syl5bb
end
