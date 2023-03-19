include "wb.mm"
include "wa.mm"
include "bothfbothsame.mm"
include "bothtbothsame.mm"
include "pm3.2i.mm"

theorem mdandyv2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vk: setvar k
  let vx: setvar x
  assume mdandyv2.1: |- ( ph <-> F. )
  assume mdandyv2.2: |- ( ps <-> T. )
  assume mdandyv2.3: |- ( ch <-> F. )
  assume mdandyv2.4: |- ( th <-> T. )
  assume mdandyv2.5: |- ( ta <-> F. )
  assume mdandyv2.6: |- ( et <-> F. )


  assert |- ( ( ( ( ch <-> ph ) /\ ( th <-> ps ) ) /\ ( ta <-> ph ) ) /\ ( et <-> ph ) )

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
    mdandyv2.3
    mdandyv2.1
    bothfbothsame
    wth
    wps
    mdandyv2.4
    mdandyv2.2
    bothtbothsame
    pm3.2i
    wta
    wph
    mdandyv2.5
    mdandyv2.1
    bothfbothsame
    pm3.2i
    wet
    wph
    mdandyv2.6
    mdandyv2.1
    bothfbothsame
    pm3.2i
end
