include "cho.mm"
include "wcel.mm"
include "w3a.mm"
include "cleo.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "cle.mm"
include "chil.mm"
include "wral.mm"
include "r19.26.mm"
include "wi.mm"
include "cr.mm"
include "hmopre.mm"
include "letr.mm"
include "syl3an.mm"
include "3anandirs.mm"
include "ralimdva.mm"
include "syl5bir.mm"
include "wb.mm"
include "leop2.mm"
include "3adant3.mm"
include "3adant1.mm"
include "anbi12d.mm"
include "3adant2.mm"
include "3imtr4d.mm"
include "imp.mm"

theorem leoptr
  let cS: class S
  let cT: class T
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vt: setvar t
  let vu: setvar u


  assert |- ( ( ( S e. HrmOp /\ T e. HrmOp /\ U e. HrmOp ) /\ ( S <_op T /\ T <_op U ) ) -> S <_op U )

  proof
    cS
    cho
    wcel
    #
    cT
    cho
    wcel
    #
    cU
    cho
    wcel
    #
    w3a
    #
    cS
    cT
    cleo
    wbr
    #
    cT
    cU
    cleo
    wbr
    #
    wa
    #
    cS
    cU
    cleo
    wbr
    #
    @3
    vx
    cv
    #
    cS
    cfv
    @8
    csp
    co
    #
    @8
    cT
    cfv
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
    @10
    @8
    cU
    cfv
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
    #
    @9
    @13
    cle
    wbr
    #
    vx
    chil
    wral
    #
    @6
    @7
    @16
    @11
    @14
    wa
    #
    vx
    chil
    wral
    @3
    @18
    @11
    @14
    vx
    chil
    r19.26
    @3
    @19
    @17
    vx
    chil
    @0
    @1
    @2
    @8
    chil
    wcel
    #
    @19
    @17
    wi
    #
    @0
    @20
    wa
    @9
    cr
    wcel
    @1
    @20
    wa
    @10
    cr
    wcel
    @2
    @20
    wa
    @13
    cr
    wcel
    @21
    @8
    cS
    hmopre
    @8
    cT
    hmopre
    @8
    cU
    hmopre
    @9
    @10
    @13
    letr
    syl3an
    3anandirs
    ralimdva
    syl5bir
    @3
    @4
    @12
    @5
    @15
    @0
    @1
    @4
    @12
    wb
    @2
    vx
    cS
    cT
    leop2
    3adant3
    @1
    @2
    @5
    @15
    wb
    @0
    vx
    cT
    cU
    leop2
    3adant1
    anbi12d
    @0
    @2
    @7
    @18
    wb
    @1
    vx
    cS
    cU
    leop2
    3adant2
    3imtr4d
    imp
end
