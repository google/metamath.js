include "chst.mm"
include "wcel.mm"
include "cch.mm"
include "wa.mm"
include "cfv.mm"
include "chil.mm"
include "cno.mm"
include "cc0.mm"
include "wceq.mm"
include "c0v.mm"
include "wb.mm"
include "hstcl.mm"
include "norm-i.mm"
include "syl.mm"

theorem hst0h
  let cA: class A
  let cS: class S
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let cB: class B


  assert |- ( ( S e. CHStates /\ A e. CH ) -> ( ( normh ` ( S ` A ) ) = 0 <-> ( S ` A ) = 0h ) )

  proof
    cS
    chst
    wcel
    cA
    cch
    wcel
    wa
    cA
    cS
    cfv
    #
    chil
    wcel
    @0
    cno
    cfv
    cc0
    wceq
    @0
    c0v
    wceq
    wb
    cA
    cS
    hstcl
    @0
    norm-i
    syl
end
