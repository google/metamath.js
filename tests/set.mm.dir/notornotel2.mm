include "wn.mm"
include "wo.mm"
include "orcom.mm"
include "sylnibr.mm"
include "notornotel1.mm"

theorem notornotel2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume notornotel2.1: |- ( ph -> -. ( ps \/ -. ch ) )


  assert |- ( ph -> ch )

  proof
    wph
    wch
    wps
    wph
    wps
    wch
    wn
    #
    wo
    @0
    wps
    wo
    notornotel2.1
    @0
    wps
    orcom
    sylnibr
    notornotel1
end
