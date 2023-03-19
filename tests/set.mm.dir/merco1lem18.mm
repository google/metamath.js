include "wi.mm"
include "wfal.mm"
include "merco1.mm"
include "merco1lem17.mm"
include "ax-mp.mm"
include "merco1lem5.mm"
include "merco1lem3.mm"
include "merco1lem4.mm"
include "merco1lem2.mm"
include "merco1lem9.mm"

theorem merco1lem18
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ( ps -> ch ) ) -> ( ( ps -> ph ) -> ( ps -> ch ) ) )

  proof
    wps
    wph
    wi
    #
    wph
    wps
    wch
    wi
    #
    wi
    #
    @0
    @1
    wi
    #
    wi
    #
    wi
    #
    @4
    @1
    wps
    wi
    #
    wph
    wi
    @4
    wi
    #
    @5
    @6
    @0
    wfal
    wi
    #
    wi
    @6
    wi
    wph
    wi
    @4
    wi
    @7
    @1
    wps
    @0
    @6
    wph
    merco1
    @6
    @8
    wph
    @4
    merco1lem17
    ax-mp
    wps
    wch
    wph
    @4
    merco1lem17
    ax-mp
    @5
    @5
    @4
    wi
    #
    wi
    #
    @9
    @3
    @4
    wfal
    wi
    @5
    wfal
    wi
    #
    wi
    #
    wfal
    wi
    #
    wfal
    wi
    #
    wi
    #
    @10
    @4
    @14
    wi
    #
    @15
    @12
    @14
    wi
    #
    @16
    @14
    wfal
    wi
    @13
    wi
    @17
    @12
    wfal
    wfal
    merco1lem5
    @14
    wfal
    @12
    merco1lem3
    ax-mp
    @4
    @11
    @14
    merco1lem5
    ax-mp
    @2
    @3
    @14
    merco1lem4
    ax-mp
    @13
    @0
    wi
    @10
    wi
    @15
    @10
    wi
    @4
    wfal
    @5
    wfal
    @0
    merco1
    @13
    @0
    @10
    @1
    merco1lem2
    ax-mp
    ax-mp
    @5
    @4
    merco1lem9
    ax-mp
    ax-mp
end
