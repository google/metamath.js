include "cr.mm"
include "wcel.mm"
include "cho.mm"
include "wa.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "ch0o.mm"
include "cleo.mm"
include "chot.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "chil.mm"
include "wral.mm"
include "cmul.mm"
include "wi.mm"
include "hmopre.mm"
include "mulge0.mm"
include "sylanr1.mm"
include "expr.mm"
include "an4s.mm"
include "anassrs.mm"
include "wb.mm"
include "cc.mm"
include "wf.mm"
include "wceq.mm"
include "recn.mm"
include "hmopf.mm"
include "anim12i.mm"
include "csm.mm"
include "homval.mm"
include "3expa.mm"
include "oveq1d.mm"
include "simpll.mm"
include "ffvelrn.mm"
include "adantll.mm"
include "simpr.mm"
include "ax-his3.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "sylan.mm"
include "breq2d.mm"
include "adantlr.mm"
include "sylibrd.mm"
include "ralimdva.mm"
include "expimpd.mm"
include "leoppos.mm"
include "adantl.mm"
include "anbi2d.mm"
include "hmopm.mm"
include "syl.mm"
include "3imtr4d.mm"
include "imp.mm"

theorem leopmuli
  let cA: class A
  let cT: class T
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let vt: setvar t
  let vu: setvar u
  let cU: class U


  assert |- ( ( ( A e. RR /\ T e. HrmOp ) /\ ( 0 <_ A /\ 0hop <_op T ) ) -> 0hop <_op ( A .op T ) )

  proof
    cA
    cr
    wcel
    #
    cT
    cho
    wcel
    #
    wa
    #
    cc0
    cA
    cle
    wbr
    #
    ch0o
    cT
    cleo
    wbr
    #
    wa
    #
    ch0o
    cA
    cT
    chot
    co
    #
    cleo
    wbr
    #
    @2
    @3
    cc0
    vx
    cv
    #
    cT
    cfv
    #
    @8
    csp
    co
    #
    cle
    wbr
    #
    vx
    chil
    wral
    #
    wa
    cc0
    @8
    @6
    cfv
    #
    @8
    csp
    co
    #
    cle
    wbr
    #
    vx
    chil
    wral
    #
    @5
    @7
    @2
    @3
    @12
    @16
    @2
    @3
    wa
    #
    @11
    @15
    vx
    chil
    @17
    @8
    chil
    wcel
    #
    wa
    @11
    cc0
    cA
    @10
    cmul
    co
    #
    cle
    wbr
    #
    @15
    @2
    @3
    @18
    @11
    @20
    wi
    #
    @0
    @3
    @1
    @18
    @21
    @0
    @3
    wa
    #
    @1
    @18
    wa
    #
    @11
    @20
    @23
    @22
    @10
    cr
    wcel
    @11
    @20
    @8
    cT
    hmopre
    cA
    @10
    mulge0
    sylanr1
    expr
    an4s
    anassrs
    @2
    @18
    @15
    @20
    wb
    @3
    @2
    @18
    wa
    @14
    @19
    cc0
    cle
    @2
    cA
    cc
    wcel
    #
    chil
    chil
    cT
    wf
    #
    wa
    #
    @18
    @14
    @19
    wceq
    @0
    @24
    @1
    @25
    cA
    recn
    cT
    hmopf
    anim12i
    @26
    @18
    wa
    #
    @14
    cA
    @9
    csm
    co
    #
    @8
    csp
    co
    #
    @19
    @27
    @13
    @28
    @8
    csp
    @24
    @25
    @18
    @13
    @28
    wceq
    cA
    @8
    cT
    homval
    3expa
    oveq1d
    @27
    @24
    @9
    chil
    wcel
    #
    @18
    @29
    @19
    wceq
    @24
    @25
    @18
    simpll
    @25
    @18
    @30
    @24
    chil
    chil
    @8
    cT
    ffvelrn
    adantll
    @26
    @18
    simpr
    cA
    @9
    @8
    ax-his3
    syl3anc
    eqtrd
    sylan
    breq2d
    adantlr
    sylibrd
    ralimdva
    expimpd
    @2
    @4
    @12
    @3
    @1
    @4
    @12
    wb
    @0
    vx
    cT
    leoppos
    adantl
    anbi2d
    @2
    @6
    cho
    wcel
    @7
    @16
    wb
    cA
    cT
    hmopm
    vx
    @6
    leoppos
    syl
    3imtr4d
    imp
end
