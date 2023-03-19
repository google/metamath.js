include "wo.mm"
include "wn.mm"
include "wi.mm"
include "orcom.mm"
include "df-or.mm"
include "sylbb.mm"
include "sylc.mm"

theorem unitresl
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume unitresl.1: |- ( ph -> ( ps \/ ch ) )
  assume unitresl.2: |- ( ph -> -. ch )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    wch
    wo
    #
    wch
    wn
    #
    wps
    unitresl.1
    unitresl.2
    @0
    wch
    wps
    wo
    @1
    wps
    wi
    wps
    wch
    orcom
    wch
    wps
    df-or
    sylbb
    sylc
end
