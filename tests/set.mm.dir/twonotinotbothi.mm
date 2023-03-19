include "wi.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "orci.mm"
include "pm3.14.mm"
include "ax-mp.mm"

theorem twonotinotbothi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vk: setvar k
  let vx: setvar x
  assume twonotinotbothi.1: |- -. ( ph -> ps )
  assume twonotinotbothi.2: |- -. ( ch -> th )


  assert |- -. ( ( ph -> ps ) /\ ( ch -> th ) )

  proof
    wph
    wps
    wi
    #
    wn
    #
    wch
    wth
    wi
    #
    wn
    #
    wo
    @0
    @2
    wa
    wn
    @1
    @3
    twonotinotbothi.1
    orci
    @0
    @2
    pm3.14
    ax-mp
end
