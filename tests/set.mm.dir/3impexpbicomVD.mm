include "w3a.mm"
include "wb.mm"
include "wi.mm"
include "idn1.mm"
include "bicom.mm"
include "imbi2.mm"
include "biimpcd.mm"
include "e10.mm"
include "3impexp.mm"
include "biimpi.mm"
include "e1a.mm"
include "in1.mm"
include "biimpri.mm"
include "biimprcd.mm"
include "impbi.mm"
include "e00.mm"

theorem 3impexpbicomVD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ( ph /\ ps /\ ch ) -> ( th <-> ta ) ) <-> ( ph -> ( ps -> ( ch -> ( ta <-> th ) ) ) ) )

  proof
    wph
    wps
    wch
    w3a
    #
    wth
    wta
    wb
    #
    wi
    #
    wph
    wps
    wch
    wta
    wth
    wb
    #
    wi
    wi
    wi
    #
    wi
    @4
    @2
    wi
    @2
    @4
    wb
    @2
    @4
    @2
    @0
    @3
    wi
    #
    @4
    @2
    @2
    @1
    @3
    wb
    #
    @5
    @2
    idn1
    wth
    wta
    bicom
    #
    @6
    @2
    @5
    @1
    @3
    @0
    imbi2
    #
    biimpcd
    e10
    @5
    @4
    wph
    wps
    wch
    @3
    3impexp
    #
    biimpi
    e1a
    in1
    @4
    @2
    @4
    @5
    @6
    @2
    @4
    @4
    @5
    @4
    idn1
    @5
    @4
    @9
    biimpri
    e1a
    @7
    @6
    @2
    @5
    @8
    biimprcd
    e10
    in1
    @2
    @4
    impbi
    e00
end
