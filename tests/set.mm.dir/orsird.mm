include "wn.mm"
include "wo.mm"
include "wa.mm"
include "ioran.mm"
include "sylib.mm"
include "simprd.mm"

theorem orsird
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume orsird.1: |- ( ph -> -. ( ps \/ ch ) )


  assert |- ( ph -> -. ch )

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
    orsird.1
    wps
    wch
    ioran
    sylib
    simprd
end
