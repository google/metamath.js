include "wo.mm"
include "wn.mm"
include "pm1.4.mm"
include "con3i.mm"
include "con1i.mm"
include "orri.mm"

theorem rb-ax2
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ( ph \/ ps ) \/ ( ps \/ ph ) )

  proof
    wph
    wps
    wo
    #
    wn
    #
    wps
    wph
    wo
    #
    @2
    @1
    @0
    @2
    wph
    wps
    pm1.4
    con3i
    con1i
    orri
end
