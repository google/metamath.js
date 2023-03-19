include "wa.mm"
include "wb.mm"
include "wi.mm"
include "idn1.mm"
include "biimpr.mm"
include "e1a.mm"
include "pm3.3.mm"
include "pm2.04.mm"
include "in1.mm"

theorem simplbi2comtVD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph <-> ( ps /\ ch ) ) -> ( ch -> ( ps -> ph ) ) )

  proof
    wph
    wps
    wch
    wa
    #
    wb
    #
    wch
    wps
    wph
    wi
    wi
    #
    @1
    wps
    wch
    wph
    wi
    wi
    #
    @2
    @1
    @0
    wph
    wi
    #
    @3
    @1
    @1
    @4
    @1
    idn1
    wph
    @0
    biimpr
    e1a
    wps
    wch
    wph
    pm3.3
    e1a
    wps
    wch
    wph
    pm2.04
    e1a
    in1
end
