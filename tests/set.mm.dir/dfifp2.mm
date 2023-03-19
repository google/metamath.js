include "wif.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wi.mm"
include "df-ifp.mm"
include "cases2.mm"
include "bitri.mm"

theorem dfifp2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( if- ( ph , ps , ch ) <-> ( ( ph -> ps ) /\ ( -. ph -> ch ) ) )

  proof
    wph
    wps
    wch
    wif
    wph
    wps
    wa
    wph
    wn
    #
    wch
    wa
    wo
    wph
    wps
    wi
    @0
    wch
    wi
    wa
    wph
    wps
    wch
    df-ifp
    wph
    wps
    wch
    cases2
    bitri
end
