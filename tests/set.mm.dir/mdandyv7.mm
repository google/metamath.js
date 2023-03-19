include "wb.mm"
include "wa.mm"
include "bothtbothsame.mm"
include "pm3.2i.mm"
include "bothfbothsame.mm"

theorem mdandyv7
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vk: setvar k
  let vx: setvar x
  assume mdandyv7.1: |- ( ph <-> F. )
  assume mdandyv7.2: |- ( ps <-> T. )
  assume mdandyv7.3: |- ( ch <-> T. )
  assume mdandyv7.4: |- ( th <-> T. )
  assume mdandyv7.5: |- ( ta <-> T. )
  assume mdandyv7.6: |- ( et <-> F. )


  assert |- ( ( ( ( ch <-> ps ) /\ ( th <-> ps ) ) /\ ( ta <-> ps ) ) /\ ( et <-> ph ) )

  proof
    wch
    wps
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
    wph
    wb
    @2
    @3
    @0
    @1
    wch
    wps
    mdandyv7.3
    mdandyv7.2
    bothtbothsame
    wth
    wps
    mdandyv7.4
    mdandyv7.2
    bothtbothsame
    pm3.2i
    wta
    wps
    mdandyv7.5
    mdandyv7.2
    bothtbothsame
    pm3.2i
    wet
    wph
    mdandyv7.6
    mdandyv7.1
    bothfbothsame
    pm3.2i
end
