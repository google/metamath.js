include "wn.mm"
include "wo.mm"
include "wa.mm"
include "ioran.mm"
include "biimpi.mm"
include "simpl.mm"
include "notnotr.mm"
include "3syl.mm"
include "syl.mm"

theorem notornotel1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume notornotel1.1: |- ( ph -> -. ( -. ps \/ ch ) )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    wn
    #
    wch
    wo
    wn
    #
    wps
    notornotel1.1
    @1
    @0
    wn
    #
    wch
    wn
    #
    wa
    #
    @2
    wps
    @1
    @4
    @0
    wch
    ioran
    biimpi
    @2
    @3
    simpl
    wps
    notnotr
    3syl
    syl
end
