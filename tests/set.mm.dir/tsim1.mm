include "wn.mm"
include "wo.mm"
include "wi.mm"
include "exmid.mm"
include "df-or.mm"
include "notnotb.mm"
include "bicomi.mm"
include "imbi1i.mm"
include "bitri.mm"
include "orbi1i.mm"
include "mpbir.mm"
include "a1i.mm"

theorem tsim1
  let wph: wff ph
  let wps: wff ps
  let wth: wff th


  assert |- ( th -> ( ( -. ph \/ ps ) \/ -. ( ph -> ps ) ) )

  proof
    wph
    wn
    #
    wps
    wo
    #
    wph
    wps
    wi
    #
    wn
    #
    wo
    #
    wth
    @4
    @2
    @3
    wo
    @2
    exmid
    @1
    @2
    @3
    @1
    @0
    wn
    #
    wps
    wi
    @2
    @0
    wps
    df-or
    @5
    wph
    wps
    wph
    @5
    wph
    notnotb
    bicomi
    imbi1i
    bitri
    orbi1i
    mpbir
    a1i
end
