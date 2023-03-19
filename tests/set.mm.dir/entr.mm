include "cen.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "wtru.mm"
include "cvv.mm"
include "wer.mm"
include "ener.mm"
include "a1i.mm"
include "ertr.mm"
include "trud.mm"

theorem entr
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h


  assert |- ( ( A ~~ B /\ B ~~ C ) -> A ~~ C )

  proof
    cA
    cB
    cen
    wbr
    cB
    cC
    cen
    wbr
    wa
    cA
    cC
    cen
    wbr
    wi
    wtru
    cA
    cB
    cC
    cen
    cvv
    cvv
    cen
    wer
    wtru
    ener
    a1i
    ertr
    trud
end
