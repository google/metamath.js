include "wo.mm"
include "wi.mm"
include "wa.mm"
include "pm2.67-2.mm"
include "olc.mm"
include "imim1i.mm"
include "jca.mm"
include "pm3.44.mm"
include "impbii.mm"

theorem jaob
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph \/ ch ) -> ps ) <-> ( ( ph -> ps ) /\ ( ch -> ps ) ) )

  proof
    wph
    wch
    wo
    #
    wps
    wi
    #
    wph
    wps
    wi
    #
    wch
    wps
    wi
    #
    wa
    @1
    @2
    @3
    wph
    wps
    wch
    pm2.67-2
    wch
    @0
    wps
    wch
    wph
    olc
    imim1i
    jca
    wps
    wph
    wch
    pm3.44
    impbii
end
