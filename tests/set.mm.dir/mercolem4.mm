include "wi.mm"
include "wfal.mm"
include "merco2.mm"
include "mercolem1.mm"
include "ax-mp.mm"
include "mercolem3.mm"

theorem mercolem4
  let wph: wff ph
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( th -> ( et -> ph ) ) -> ( ( ( th -> ch ) -> ph ) -> ( ta -> ( et -> ph ) ) ) )

  proof
    wph
    wph
    wi
    #
    wfal
    wph
    wi
    #
    wph
    wi
    wi
    @0
    wph
    @0
    wi
    wi
    wi
    #
    wth
    wet
    wph
    wi
    #
    wi
    #
    wth
    wch
    wi
    #
    wph
    wi
    #
    wta
    @3
    wi
    wi
    #
    wi
    #
    wph
    wph
    wph
    wph
    wph
    wph
    merco2
    #
    @2
    @2
    @8
    wi
    #
    @9
    @3
    wph
    wi
    #
    @1
    wth
    wi
    wi
    #
    @8
    wi
    #
    @2
    @10
    wi
    #
    @3
    wph
    wph
    wth
    @6
    wta
    merco2
    @8
    wth
    wi
    #
    @1
    @12
    wi
    wi
    #
    @13
    @14
    wi
    @15
    @12
    wi
    #
    @16
    @5
    @1
    @8
    wi
    wi
    #
    @17
    @1
    @5
    wi
    #
    @8
    wi
    #
    @18
    @0
    @19
    wi
    @7
    wi
    @20
    wph
    wph
    wph
    @5
    wta
    wet
    merco2
    @0
    @19
    @7
    @4
    mercolem1
    ax-mp
    @1
    @5
    @8
    @1
    mercolem1
    ax-mp
    wth
    wch
    wph
    @8
    @11
    @1
    merco2
    ax-mp
    @1
    @15
    @12
    mercolem3
    ax-mp
    @8
    wth
    wph
    @12
    @2
    @2
    merco2
    ax-mp
    ax-mp
    ax-mp
    ax-mp
end
