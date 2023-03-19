include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wif.mm"
include "anbi12d.mm"
include "notbid.mm"
include "orbi12d.mm"
include "df-ifp.mm"
include "3bitr4g.mm"

theorem ifpbi123d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  assume ifpbi123d.1: |- ( ph -> ( ps <-> ta ) )
  assume ifpbi123d.2: |- ( ph -> ( ch <-> et ) )
  assume ifpbi123d.3: |- ( ph -> ( th <-> ze ) )


  assert |- ( ph -> ( if- ( ps , ch , th ) <-> if- ( ta , et , ze ) ) )

  proof
    wph
    wps
    wch
    wa
    #
    wps
    wn
    #
    wth
    wa
    #
    wo
    wta
    wet
    wa
    #
    wta
    wn
    #
    wze
    wa
    #
    wo
    wps
    wch
    wth
    wif
    wta
    wet
    wze
    wif
    wph
    @0
    @3
    @2
    @5
    wph
    wps
    wta
    wch
    wet
    ifpbi123d.1
    ifpbi123d.2
    anbi12d
    wph
    @1
    @4
    wth
    wze
    wph
    wps
    wta
    ifpbi123d.1
    notbid
    ifpbi123d.3
    anbi12d
    orbi12d
    wps
    wch
    wth
    df-ifp
    wta
    wet
    wze
    df-ifp
    3bitr4g
end
