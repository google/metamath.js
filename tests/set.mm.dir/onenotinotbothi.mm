include "wi.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "orci.mm"
include "pm3.14.mm"
include "ax-mp.mm"

theorem onenotinotbothi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vk: setvar k
  let vx: setvar x
  assume onenotinotbothi.1: |- -. ( ph -> ps )


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
    onenotinotbothi.1
    orci
    @0
    @2
    pm3.14
    ax-mp
end
