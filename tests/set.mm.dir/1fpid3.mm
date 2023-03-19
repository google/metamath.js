include "wif.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "df-ifp.mm"
include "simpr.mm"
include "jaoi.mm"
include "sylbi.mm"

theorem 1fpid3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume 1fpid3.1: |- ( ( ph /\ ps ) -> ch )


  assert |- ( if- ( ph , ps , ch ) -> ch )

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
    wch
    wph
    wps
    wch
    df-ifp
    @0
    wch
    @2
    1fpid3.1
    @1
    wch
    simpr
    jaoi
    sylbi
end
