include "wb.mm"
include "wa.mm"
include "bothtbothsame.mm"
include "bothfbothsame.mm"
include "pm3.2i.mm"

theorem mdandyv1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vk: setvar k
  let vx: setvar x
  assume mdandyv1.1: |- ( ph <-> F. )
  assume mdandyv1.2: |- ( ps <-> T. )
  assume mdandyv1.3: |- ( ch <-> T. )
  assume mdandyv1.4: |- ( th <-> F. )
  assume mdandyv1.5: |- ( ta <-> F. )
  assume mdandyv1.6: |- ( et <-> F. )


  assert |- ( ( ( ( ch <-> ps ) /\ ( th <-> ph ) ) /\ ( ta <-> ph ) ) /\ ( et <-> ph ) )

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
    wph
    wb
    @2
    @3
    @0
    @1
    wch
    wps
    mdandyv1.3
    mdandyv1.2
    bothtbothsame
    wth
    wph
    mdandyv1.4
    mdandyv1.1
    bothfbothsame
    pm3.2i
    wta
    wph
    mdandyv1.5
    mdandyv1.1
    bothfbothsame
    pm3.2i
    wet
    wph
    mdandyv1.6
    mdandyv1.1
    bothfbothsame
    pm3.2i
end
