include "wb.mm"
include "wa.mm"
include "bothtbothsame.mm"
include "pm3.2i.mm"
include "bothfbothsame.mm"

theorem mdandyv3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vk: setvar k
  let vx: setvar x
  assume mdandyv3.1: |- ( ph <-> F. )
  assume mdandyv3.2: |- ( ps <-> T. )
  assume mdandyv3.3: |- ( ch <-> T. )
  assume mdandyv3.4: |- ( th <-> T. )
  assume mdandyv3.5: |- ( ta <-> F. )
  assume mdandyv3.6: |- ( et <-> F. )


  assert |- ( ( ( ( ch <-> ps ) /\ ( th <-> ps ) ) /\ ( ta <-> ph ) ) /\ ( et <-> ph ) )

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
    wps
    mdandyv3.3
    mdandyv3.2
    bothtbothsame
    wth
    wps
    mdandyv3.4
    mdandyv3.2
    bothtbothsame
    pm3.2i
    wta
    wph
    mdandyv3.5
    mdandyv3.1
    bothfbothsame
    pm3.2i
    wet
    wph
    mdandyv3.6
    mdandyv3.1
    bothfbothsame
    pm3.2i
end
