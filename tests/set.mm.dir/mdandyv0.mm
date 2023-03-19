include "wb.mm"
include "wa.mm"
include "bothfbothsame.mm"
include "pm3.2i.mm"

theorem mdandyv0
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vk: setvar k
  let vx: setvar x
  assume mdandyv0.1: |- ( ph <-> F. )
  assume mdandyv0.2: |- ( ps <-> T. )
  assume mdandyv0.3: |- ( ch <-> F. )
  assume mdandyv0.4: |- ( th <-> F. )
  assume mdandyv0.5: |- ( ta <-> F. )
  assume mdandyv0.6: |- ( et <-> F. )


  assert |- ( ( ( ( ch <-> ph ) /\ ( th <-> ph ) ) /\ ( ta <-> ph ) ) /\ ( et <-> ph ) )

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
    wph
    wb
    @2
    @3
    @0
    @1
    wch
    wph
    mdandyv0.3
    mdandyv0.1
    bothfbothsame
    wth
    wph
    mdandyv0.4
    mdandyv0.1
    bothfbothsame
    pm3.2i
    wta
    wph
    mdandyv0.5
    mdandyv0.1
    bothfbothsame
    pm3.2i
    wet
    wph
    mdandyv0.6
    mdandyv0.1
    bothfbothsame
    pm3.2i
end
