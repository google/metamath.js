include "wb.mm"
include "wa.mm"
include "bothfbothsame.mm"
include "bothtbothsame.mm"
include "pm3.2i.mm"

theorem mdandyv6
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vk: setvar k
  let vx: setvar x
  assume mdandyv6.1: |- ( ph <-> F. )
  assume mdandyv6.2: |- ( ps <-> T. )
  assume mdandyv6.3: |- ( ch <-> F. )
  assume mdandyv6.4: |- ( th <-> T. )
  assume mdandyv6.5: |- ( ta <-> T. )
  assume mdandyv6.6: |- ( et <-> F. )


  assert |- ( ( ( ( ch <-> ph ) /\ ( th <-> ps ) ) /\ ( ta <-> ps ) ) /\ ( et <-> ph ) )

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
    wph
    wb
    @2
    @3
    @0
    @1
    wch
    wph
    mdandyv6.3
    mdandyv6.1
    bothfbothsame
    wth
    wps
    mdandyv6.4
    mdandyv6.2
    bothtbothsame
    pm3.2i
    wta
    wps
    mdandyv6.5
    mdandyv6.2
    bothtbothsame
    pm3.2i
    wet
    wph
    mdandyv6.6
    mdandyv6.1
    bothfbothsame
    pm3.2i
end
