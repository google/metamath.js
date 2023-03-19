include "cxp.mm"
include "cpw.mm"
include "cpm.mm"
include "co.mm"
include "wunxp.mm"
include "wunpw.mm"
include "wss.mm"
include "pmsspw.mm"
include "a1i.mm"
include "wunss.mm"

theorem wunpm
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume wun0.1: |- ( ph -> U e. WUni )
  assume wunop.2: |- ( ph -> A e. U )
  assume wunop.3: |- ( ph -> B e. U )


  assert |- ( ph -> ( A ^pm B ) e. U )

  proof
    wph
    cB
    cA
    cxp
    #
    cpw
    #
    cA
    cB
    cpm
    co
    #
    cU
    wun0.1
    wph
    @0
    cU
    wun0.1
    wph
    cB
    cA
    cU
    wun0.1
    wunop.3
    wunop.2
    wunxp
    wunpw
    @2
    @1
    wss
    wph
    cA
    cB
    pmsspw
    a1i
    wunss
end
