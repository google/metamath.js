include "wb.mm"
include "wa.mm"
include "bothfbothsame.mm"
include "pm3.2i.mm"
include "bothtbothsame.mm"

theorem mdandyv8
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vk: setvar k
  let vx: setvar x
  assume mdandyv8.1: |- ( ph <-> F. )
  assume mdandyv8.2: |- ( ps <-> T. )
  assume mdandyv8.3: |- ( ch <-> F. )
  assume mdandyv8.4: |- ( th <-> F. )
  assume mdandyv8.5: |- ( ta <-> F. )
  assume mdandyv8.6: |- ( et <-> T. )


  assert |- ( ( ( ( ch <-> ph ) /\ ( th <-> ph ) ) /\ ( ta <-> ph ) ) /\ ( et <-> ps ) )

  proof
    wch
    wph
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
    wph
    mdandyv8.3
    mdandyv8.1
    bothfbothsame
    wth
    wph
    mdandyv8.4
    mdandyv8.1
    bothfbothsame
    pm3.2i
    wta
    wph
    mdandyv8.5
    mdandyv8.1
    bothfbothsame
    pm3.2i
    wet
    wps
    mdandyv8.6
    mdandyv8.2
    bothtbothsame
    pm3.2i
end
