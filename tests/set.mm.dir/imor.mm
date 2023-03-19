include "wi.mm"
include "wn.mm"
include "wo.mm"
include "notnotb.mm"
include "imbi1i.mm"
include "df-or.mm"
include "bitr4i.mm"

theorem imor
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ps ) <-> ( -. ph \/ ps ) )

  proof
    wph
    wps
    wi
    wph
    wn
    #
    wn
    #
    wps
    wi
    @0
    wps
    wo
    wph
    @1
    wps
    wph
    notnotb
    imbi1i
    @0
    wps
    df-or
    bitr4i
end
