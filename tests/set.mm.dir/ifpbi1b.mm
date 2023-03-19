include "wif.mm"
include "wi.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "id.mm"
include "olci.mm"
include "pm3.2i.mm"
include "ifpim123g.mm"
include "mpbir2an.mm"
include "impbii.mm"

theorem ifpbi1b
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( if- ( ph , ch , ch ) <-> if- ( ps , ch , ch ) )

  proof
    wph
    wch
    wch
    wif
    #
    wps
    wch
    wch
    wif
    #
    @0
    @1
    wi
    wph
    wps
    wn
    #
    wi
    #
    wch
    wch
    wi
    #
    wo
    #
    wps
    wph
    wi
    #
    @4
    wo
    #
    wa
    wph
    wps
    wi
    #
    @4
    wo
    #
    @2
    wph
    wi
    #
    @4
    wo
    #
    wa
    @5
    @7
    @4
    @3
    wch
    id
    #
    olci
    @4
    @6
    @12
    olci
    #
    pm3.2i
    @9
    @11
    @4
    @8
    @12
    olci
    #
    @4
    @10
    @12
    olci
    pm3.2i
    wph
    wps
    wch
    wch
    wch
    wch
    ifpim123g
    mpbir2an
    @1
    @0
    wi
    wps
    wph
    wn
    #
    wi
    #
    @4
    wo
    #
    @9
    wa
    @7
    @15
    wps
    wi
    #
    @4
    wo
    #
    wa
    @17
    @9
    @4
    @16
    @12
    olci
    @14
    pm3.2i
    @7
    @19
    @13
    @4
    @18
    @12
    olci
    pm3.2i
    wps
    wph
    wch
    wch
    wch
    wch
    ifpim123g
    mpbir2an
    impbii
end
