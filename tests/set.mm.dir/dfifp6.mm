include "wif.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wi.mm"
include "df-ifp.mm"
include "ancom.mm"
include "annim.mm"
include "bitri.mm"
include "orbi2i.mm"

theorem dfifp6
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( if- ( ph , ps , ch ) <-> ( ( ph /\ ps ) \/ -. ( ch -> ph ) ) )

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
    @0
    wch
    wph
    wi
    wn
    #
    wo
    wph
    wps
    wch
    df-ifp
    @2
    @3
    @0
    @2
    wch
    @1
    wa
    @3
    @1
    wch
    ancom
    wch
    wph
    annim
    bitri
    orbi2i
    bitri
end
