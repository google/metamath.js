include "wi.mm"
include "wa.mm"
include "wn.mm"
include "wb.mm"
include "wif.mm"
include "ax-frege28.mm"
include "anim2i.mm"
include "con4.mm"
include "impbii.mm"
include "dfbi2.mm"
include "dfifp2.mm"
include "3bitr4i.mm"

theorem frege54cor0a
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ps <-> ph ) <-> if- ( ps , ph , -. ph ) )

  proof
    wps
    wph
    wi
    #
    wph
    wps
    wi
    #
    wa
    #
    @0
    wps
    wn
    wph
    wn
    #
    wi
    #
    wa
    #
    wps
    wph
    wb
    wps
    wph
    @3
    wif
    @2
    @5
    @1
    @4
    @0
    wph
    wps
    ax-frege28
    anim2i
    @4
    @1
    @0
    wps
    wph
    con4
    anim2i
    impbii
    wps
    wph
    dfbi2
    wps
    wph
    @3
    dfifp2
    3bitr4i
end
