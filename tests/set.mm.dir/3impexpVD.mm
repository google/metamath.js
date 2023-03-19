include "w3a.mm"
include "wi.mm"
include "wb.mm"
include "wa.mm"
include "idn1.mm"
include "df-3an.mm"
include "imbi1.mm"
include "biimpcd.mm"
include "e10.mm"
include "pm3.3.mm"
include "e1a.mm"
include "in1.mm"
include "pm3.31.mm"
include "biimprd.mm"
include "e01.mm"
include "impbi.mm"
include "e00.mm"

theorem 3impexpVD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ph /\ ps /\ ch ) -> th ) <-> ( ph -> ( ps -> ( ch -> th ) ) ) )

  proof
    wph
    wps
    wch
    w3a
    #
    wth
    wi
    #
    wph
    wps
    wch
    wth
    wi
    #
    wi
    wi
    #
    wi
    @3
    @1
    wi
    @1
    @3
    wb
    @1
    @3
    @1
    wph
    wps
    wa
    #
    @2
    wi
    #
    @3
    @1
    @4
    wch
    wa
    #
    wth
    wi
    #
    @5
    @1
    @1
    @0
    @6
    wb
    #
    @7
    @1
    idn1
    wph
    wps
    wch
    df-3an
    #
    @8
    @1
    @7
    @0
    @6
    wth
    imbi1
    #
    biimpcd
    e10
    @4
    wch
    wth
    pm3.3
    e1a
    wph
    wps
    @2
    pm3.3
    e1a
    in1
    @3
    @1
    @8
    @3
    @7
    @1
    @9
    @3
    @5
    @7
    @3
    @3
    @5
    @3
    idn1
    wph
    wps
    @2
    pm3.31
    e1a
    @4
    wch
    wth
    pm3.31
    e1a
    @8
    @1
    @7
    @10
    biimprd
    e01
    in1
    @1
    @3
    impbi
    e00
end
