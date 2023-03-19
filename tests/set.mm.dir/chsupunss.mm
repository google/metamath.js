include "cch.mm"
include "wss.mm"
include "chil.mm"
include "cpw.mm"
include "cuni.mm"
include "chsup.mm"
include "cfv.mm"
include "chsspwh.mm"
include "sstr.mm"
include "mpan2.mm"
include "hsupunss.mm"
include "syl.mm"

theorem chsupunss
  let cA: class A
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( A C_ CH -> U. A C_ ( \/H ` A ) )

  proof
    cA
    cch
    wss
    #
    cA
    chil
    cpw
    #
    wss
    #
    cA
    cuni
    cA
    chsup
    cfv
    wss
    @0
    cch
    @1
    wss
    @2
    chsspwh
    cA
    cch
    @1
    sstr
    mpan2
    cA
    hsupunss
    syl
end
