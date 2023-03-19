include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cfil.mm"
include "wf.mm"
include "w3a.mm"
include "cfcf.mm"
include "co.mm"
include "wa.mm"
include "cuni.mm"
include "cfm.mm"
include "cfcls.mm"
include "fcfval.mm"
include "eleq2d.mm"
include "eqid.mm"
include "fclselbas.mm"
include "syl6bi.mm"
include "imp.mm"
include "wceq.mm"
include "simpl1.mm"
include "toponuni.mm"
include "syl.mm"
include "eleqtrrd.mm"

theorem fcfelbas
  let cA: class A
  let cF: class F
  let cJ: class J
  let cL: class L
  let cX: class X
  let cY: class Y
  let vn: setvar n
  let vo: setvar o
  let vx: setvar x
  let vf: setvar f
  let vg: setvar g
  let vj: setvar j
  let vs: setvar s
  let vy: setvar y
  let cN: class N
  let cS: class S


  assert |- ( ( ( J e. ( TopOn ` X ) /\ L e. ( Fil ` Y ) /\ F : Y --> X ) /\ A e. ( ( J fClusf L ) ` F ) ) -> A e. X )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cL
    cY
    cfil
    cfv
    wcel
    #
    cY
    cX
    cF
    wf
    #
    w3a
    #
    cA
    cF
    cJ
    cL
    cfcf
    co
    cfv
    #
    wcel
    #
    wa
    #
    cA
    cJ
    cuni
    #
    cX
    @3
    @5
    cA
    @7
    wcel
    #
    @3
    @5
    cA
    cJ
    cL
    cX
    cF
    cfm
    co
    cfv
    #
    cfcls
    co
    #
    wcel
    @8
    @3
    @4
    @10
    cA
    cF
    cJ
    cL
    cX
    cY
    fcfval
    eleq2d
    cA
    @9
    cJ
    @7
    @7
    eqid
    fclselbas
    syl6bi
    imp
    @6
    @0
    cX
    @7
    wceq
    @0
    @1
    @2
    @5
    simpl1
    cX
    cJ
    toponuni
    syl
    eleqtrrd
end
