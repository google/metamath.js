include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cfil.mm"
include "wf.mm"
include "w3a.mm"
include "cfcf.mm"
include "co.mm"
include "csn.mm"
include "cnei.mm"
include "cima.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "wi.mm"
include "fcfnei.mm"
include "wceq.mm"
include "ineq1.mm"
include "neeq1d.mm"
include "imaeq2.mm"
include "ineq2d.mm"
include "rspc2v.mm"
include "ex.mm"
include "com3r.mm"
include "adantl.mm"
include "syl6bi.mm"
include "3imp2.mm"

theorem fcfneii
  let cA: class A
  let cS: class S
  let cF: class F
  let cJ: class J
  let cL: class L
  let cN: class N
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


  assert |- ( ( ( J e. ( TopOn ` X ) /\ L e. ( Fil ` Y ) /\ F : Y --> X ) /\ ( A e. ( ( J fClusf L ) ` F ) /\ N e. ( ( nei ` J ) ` { A } ) /\ S e. L ) ) -> ( N i^i ( F " S ) ) =/= (/) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    cL
    cY
    cfil
    cfv
    wcel
    cY
    cX
    cF
    wf
    w3a
    #
    cA
    cF
    cJ
    cL
    cfcf
    co
    cfv
    wcel
    #
    cN
    cA
    csn
    cJ
    cnei
    cfv
    cfv
    #
    wcel
    #
    cS
    cL
    wcel
    #
    cN
    cF
    cS
    cima
    #
    cin
    #
    c0
    wne
    #
    @0
    @1
    cA
    cX
    wcel
    #
    vn
    cv
    #
    cF
    vs
    cv
    #
    cima
    #
    cin
    #
    c0
    wne
    #
    vs
    cL
    wral
    vn
    @2
    wral
    #
    wa
    @3
    @4
    @7
    wi
    wi
    #
    cA
    vn
    cF
    cJ
    cL
    cX
    cY
    vs
    fcfnei
    @14
    @15
    @8
    @3
    @4
    @14
    @7
    @3
    @4
    @14
    @7
    wi
    @13
    @7
    cN
    @11
    cin
    #
    c0
    wne
    vn
    vs
    cN
    cS
    @2
    cL
    @9
    cN
    wceq
    @12
    @16
    c0
    @9
    cN
    @11
    ineq1
    neeq1d
    @10
    cS
    wceq
    #
    @16
    @6
    c0
    @17
    @11
    @5
    cN
    @10
    cS
    cF
    imaeq2
    ineq2d
    neeq1d
    rspc2v
    ex
    com3r
    adantl
    syl6bi
    3imp2
end
