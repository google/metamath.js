include "cbo.mm"
include "wcel.mm"
include "clo.mm"
include "chil.mm"
include "wf.mm"
include "bdopln.mm"
include "lnopf.mm"
include "syl.mm"

theorem bdopf
  let cT: class T
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( T e. BndLinOp -> T : ~H --> ~H )

  proof
    cT
    cbo
    wcel
    cT
    clo
    wcel
    chil
    chil
    cT
    wf
    cT
    bdopln
    cT
    lnopf
    syl
end
