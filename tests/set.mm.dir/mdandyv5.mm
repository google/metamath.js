include "wb.mm"
include "wa.mm"
include "bothtbothsame.mm"
include "bothfbothsame.mm"
include "pm3.2i.mm"

theorem mdandyv5
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vk: setvar k
  let vx: setvar x
  assume mdandyv5.1: |- ( ph <-> F. )
  assume mdandyv5.2: |- ( ps <-> T. )
  assume mdandyv5.3: |- ( ch <-> T. )
  assume mdandyv5.4: |- ( th <-> F. )
  assume mdandyv5.5: |- ( ta <-> T. )
  assume mdandyv5.6: |- ( et <-> F. )


  assert |- ( ( ( ( ch <-> ps ) /\ ( th <-> ph ) ) /\ ( ta <-> ps ) ) /\ ( et <-> ph ) )

  proof
    wch
    wps
    wb
    #
    wth
    wph
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
    mdandyv5.3
    mdandyv5.2
    bothtbothsame
    wth
    wph
    mdandyv5.4
    mdandyv5.1
    bothfbothsame
    pm3.2i
    wta
    wps
    mdandyv5.5
    mdandyv5.2
    bothtbothsame
    pm3.2i
    wet
    wph
    mdandyv5.6
    mdandyv5.1
    bothfbothsame
    pm3.2i
end
