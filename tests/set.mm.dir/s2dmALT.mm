include "wcel.mm"
include "wa.mm"
include "cs2.mm"
include "cdm.mm"
include "cc0.mm"
include "cop.mm"
include "c1.mm"
include "cpr.mm"
include "s2prop.mm"
include "dmeqd.mm"
include "dmpropg.mm"
include "eqtrd.mm"

theorem s2dmALT
  let cA: class A
  let cB: class B
  let cS: class S


  assert |- ( ( A e. S /\ B e. S ) -> dom <" A B "> = { 0 , 1 } )

  proof
    cA
    cS
    wcel
    cB
    cS
    wcel
    wa
    #
    cA
    cB
    cs2
    #
    cdm
    cc0
    cA
    cop
    c1
    cB
    cop
    cpr
    #
    cdm
    cc0
    c1
    cpr
    @0
    @1
    @2
    cA
    cB
    cS
    s2prop
    dmeqd
    cc0
    cA
    c1
    cB
    cS
    cS
    dmpropg
    eqtrd
end
