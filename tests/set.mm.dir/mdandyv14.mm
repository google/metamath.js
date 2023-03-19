include "wb.mm"
include "wa.mm"
include "bothfbothsame.mm"
include "bothtbothsame.mm"
include "pm3.2i.mm"

theorem mdandyv14
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vk: setvar k
  let vx: setvar x
  assume mdandyv14.1: |- ( ph <-> F. )
  assume mdandyv14.2: |- ( ps <-> T. )
  assume mdandyv14.3: |- ( ch <-> F. )
  assume mdandyv14.4: |- ( th <-> T. )
  assume mdandyv14.5: |- ( ta <-> T. )
  assume mdandyv14.6: |- ( et <-> T. )


  assert |- ( ( ( ( ch <-> ph ) /\ ( th <-> ps ) ) /\ ( ta <-> ps ) ) /\ ( et <-> ps ) )

  proof
    wch
    wph
    wb
    #
    wth
    wps
    wb
    #
    wa
    #
    wta
    wps
    wb
    #
    wa
    wet
    wps
    wb
    @2
    @3
    @0
    @1
    wch
    wph
    mdandyv14.3
    mdandyv14.1
    bothfbothsame
    wth
    wps
    mdandyv14.4
    mdandyv14.2
    bothtbothsame
    pm3.2i
    wta
    wps
    mdandyv14.5
    mdandyv14.2
    bothtbothsame
    pm3.2i
    wet
    wps
    mdandyv14.6
    mdandyv14.2
    bothtbothsame
    pm3.2i
end
