include "wn.mm"
include "wo.mm"
include "wa.mm"
include "ioran.mm"
include "sylib.mm"
include "simpld.mm"

theorem orsild
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume orsild.1: |- ( ph -> -. ( ps \/ ch ) )


  assert |- ( ph -> -. ps )

  proof
    wph
    wps
    wn
    #
    wch
    wn
    #
    wph
    wps
    wch
    wo
    wn
    @0
    @1
    wa
    orsild.1
    wps
    wch
    ioran
    sylib
    simpld
end
