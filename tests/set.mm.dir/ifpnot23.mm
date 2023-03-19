include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wif.mm"
include "ianor.mm"
include "pm4.55.mm"
include "anbi12i.mm"
include "ioran.mm"
include "dfifp4.mm"
include "3bitr4i.mm"
include "df-ifp.mm"
include "xchnxbir.mm"

theorem ifpnot23
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( -. if- ( ph , ps , ch ) <-> if- ( ph , -. ps , -. ch ) )

  proof
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
    #
    wph
    wps
    wn
    #
    wch
    wn
    #
    wif
    #
    wph
    wps
    wch
    wif
    @0
    wn
    #
    @2
    wn
    #
    wa
    @1
    @4
    wo
    #
    wph
    @5
    wo
    #
    wa
    @3
    wn
    @6
    @7
    @9
    @8
    @10
    wph
    wps
    ianor
    wph
    wch
    pm4.55
    anbi12i
    @0
    @2
    ioran
    wph
    @4
    @5
    dfifp4
    3bitr4i
    wph
    wps
    wch
    df-ifp
    xchnxbir
end
