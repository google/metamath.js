include "wb.mm"
include "wa.mm"
include "bothtbothsame.mm"
include "bothfbothsame.mm"
include "pm3.2i.mm"

theorem mdandyv9
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vk: setvar k
  let vx: setvar x
  assume mdandyv9.1: |- ( ph <-> F. )
  assume mdandyv9.2: |- ( ps <-> T. )
  assume mdandyv9.3: |- ( ch <-> T. )
  assume mdandyv9.4: |- ( th <-> F. )
  assume mdandyv9.5: |- ( ta <-> F. )
  assume mdandyv9.6: |- ( et <-> T. )


  assert |- ( ( ( ( ch <-> ps ) /\ ( th <-> ph ) ) /\ ( ta <-> ph ) ) /\ ( et <-> ps ) )

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
    wph
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
    wps
    mdandyv9.3
    mdandyv9.2
    bothtbothsame
    wth
    wph
    mdandyv9.4
    mdandyv9.1
    bothfbothsame
    pm3.2i
    wta
    wph
    mdandyv9.5
    mdandyv9.1
    bothfbothsame
    pm3.2i
    wet
    wps
    mdandyv9.6
    mdandyv9.2
    bothtbothsame
    pm3.2i
end
