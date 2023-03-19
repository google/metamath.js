include "wif.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "df-ifp.mm"
include "simpr.mm"
include "orim12i.mm"
include "sylbi.mm"

theorem ifpor
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( if- ( ph , ps , ch ) -> ( ps \/ ch ) )

  proof
    wph
    wps
    wch
    wif
    wph
    wps
    wa
    #
    wph
    wn
    #
    wch
    wa
    #
    wo
    wps
    wch
    wo
    wph
    wps
    wch
    df-ifp
    @0
    wps
    @2
    wch
    wph
    wps
    simpr
    @1
    wch
    simpr
    orim12i
    sylbi
end
