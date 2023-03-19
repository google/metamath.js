include "cun.mm"
include "cpw.mm"
include "cxp.mm"
include "wunun.mm"
include "wunpw.mm"
include "wss.mm"
include "xpsspw.mm"
include "a1i.mm"
include "wunss.mm"

theorem wunxp
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


  assert |- ( ph -> ( A X. B ) e. U )

  proof
    wph
    cA
    cB
    cun
    #
    cpw
    #
    cpw
    #
    cA
    cB
    cxp
    #
    cU
    wun0.1
    wph
    @1
    cU
    wun0.1
    wph
    @0
    cU
    wun0.1
    wph
    cA
    cB
    cU
    wun0.1
    wunop.2
    wunop.3
    wunun
    wunpw
    wunpw
    @3
    @2
    wss
    wph
    cA
    cB
    xpsspw
    a1i
    wunss
end
