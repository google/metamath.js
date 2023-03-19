include "wn.mm"
include "wo.mm"
include "wi.mm"
include "orim2.mm"
include "imor.mm"
include "3imtr3i.mm"
include "imori.mm"

theorem rb-ax1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( -. ( -. ps \/ ch ) \/ ( -. ( ph \/ ps ) \/ ( ph \/ ch ) ) )

  proof
    wps
    wn
    wch
    wo
    #
    wph
    wps
    wo
    #
    wn
    wph
    wch
    wo
    #
    wo
    #
    wps
    wch
    wi
    @1
    @2
    wi
    @0
    @3
    wph
    wps
    wch
    orim2
    wps
    wch
    imor
    @1
    @2
    imor
    3imtr3i
    imori
end
