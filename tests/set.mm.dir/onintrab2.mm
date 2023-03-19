include "con0.mm"
include "wrex.mm"
include "crab.mm"
include "cint.mm"
include "cvv.mm"
include "wcel.mm"
include "intexrab.mm"
include "onintrab.mm"
include "bitri.mm"

theorem onintrab2
  let wph: wff ph
  let vx: setvar x


  assert |- ( E. x e. On ph <-> |^| { x e. On | ph } e. On )

  proof
    wph
    vx
    con0
    wrex
    wph
    vx
    con0
    crab
    cint
    #
    cvv
    wcel
    @0
    con0
    wcel
    wph
    vx
    con0
    intexrab
    wph
    vx
    onintrab
    bitri
end
