include "csalg.mm"
include "wcel.mm"
include "wtru.mm"
include "ctop.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "retop.mm"
include "eqeltri.mm"
include "a1i.mm"
include "salgencld.mm"
include "trud.mm"

theorem bor1sal
  let cB: class B
  let cJ: class J
  let vk: setvar k
  let vx: setvar x
  assume bor1sal.t: |- J = ( topGen ` ran (,) )
  assume bor1sal.b: |- B = ( SalGen ` J )


  assert |- B e. SAlg

  proof
    cB
    csalg
    wcel
    wtru
    cB
    ctop
    cJ
    cJ
    ctop
    wcel
    wtru
    cJ
    cioo
    crn
    ctg
    cfv
    ctop
    bor1sal.t
    retop
    eqeltri
    a1i
    bor1sal.b
    salgencld
    trud
end
