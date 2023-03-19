include "cado.mm"
include "cdm.mm"
include "wcel.mm"
include "chil.mm"
include "cfv.mm"
include "wf.mm"
include "dmadjrn.mm"
include "dmadjop.mm"
include "syl.mm"
include "ffvelrnda.mm"

theorem adjcl
  let cA: class A
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cS: class S


  assert |- ( ( T e. dom adjh /\ A e. ~H ) -> ( ( adjh ` T ) ` A ) e. ~H )

  proof
    cT
    cado
    cdm
    #
    wcel
    #
    chil
    chil
    cA
    cT
    cado
    cfv
    #
    @1
    @2
    @0
    wcel
    chil
    chil
    @2
    wf
    cT
    dmadjrn
    @2
    dmadjop
    syl
    ffvelrnda
end
