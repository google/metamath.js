include "chil.mm"
include "wf.mm"
include "cei.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "c0v.mm"
include "wne.mm"
include "csn.mm"
include "cspn.mm"
include "w3a.mm"
include "eleigvec2.mm"
include "biimpa.mm"
include "simp1d.mm"

theorem eleigveccl
  let cA: class A
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cS: class S


  assert |- ( ( T : ~H --> ~H /\ A e. ( eigvec ` T ) ) -> A e. ~H )

  proof
    chil
    chil
    cT
    wf
    #
    cA
    cT
    cei
    cfv
    wcel
    #
    wa
    cA
    chil
    wcel
    #
    cA
    c0v
    wne
    #
    cA
    cT
    cfv
    cA
    csn
    cspn
    cfv
    wcel
    #
    @0
    @1
    @2
    @3
    @4
    w3a
    cA
    cT
    eleigvec2
    biimpa
    simp1d
end
