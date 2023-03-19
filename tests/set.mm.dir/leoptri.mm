include "cho.mm"
include "wcel.mm"
include "wa.mm"
include "cleo.mm"
include "wbr.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "cle.mm"
include "chil.mm"
include "wral.mm"
include "wceq.mm"
include "leop2.mm"
include "wb.mm"
include "ancoms.mm"
include "anbi12d.mm"
include "cr.mm"
include "hmopre.mm"
include "adantlr.mm"
include "adantll.mm"
include "letri3d.mm"
include "ralbidva.mm"
include "r19.26.mm"
include "syl6rbb.mm"
include "clo.mm"
include "hmoplin.mm"
include "lnopeq.mm"
include "syl2an.mm"
include "3bitrd.mm"

theorem leoptri
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
  let cS: class S
  let vt: setvar t
  let vu: setvar u


  assert |- ( ( T e. HrmOp /\ U e. HrmOp ) -> ( ( T <_op U /\ U <_op T ) <-> T = U ) )

  proof
    cT
    cho
    wcel
    #
    cU
    cho
    wcel
    #
    wa
    #
    cT
    cU
    cleo
    wbr
    #
    cU
    cT
    cleo
    wbr
    #
    wa
    vx
    cv
    #
    cT
    cfv
    @5
    csp
    co
    #
    @5
    cU
    cfv
    @5
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
    @7
    @6
    cle
    wbr
    #
    vx
    chil
    wral
    #
    wa
    #
    @6
    @7
    wceq
    #
    vx
    chil
    wral
    #
    cT
    cU
    wceq
    #
    @2
    @3
    @9
    @4
    @11
    vx
    cT
    cU
    leop2
    @1
    @0
    @4
    @11
    wb
    vx
    cU
    cT
    leop2
    ancoms
    anbi12d
    @2
    @14
    @8
    @10
    wa
    #
    vx
    chil
    wral
    @12
    @2
    @13
    @16
    vx
    chil
    @2
    @5
    chil
    wcel
    #
    wa
    @6
    @7
    @0
    @17
    @6
    cr
    wcel
    @1
    @5
    cT
    hmopre
    adantlr
    @1
    @17
    @7
    cr
    wcel
    @0
    @5
    cU
    hmopre
    adantll
    letri3d
    ralbidva
    @8
    @10
    vx
    chil
    r19.26
    syl6rbb
    @0
    cT
    clo
    wcel
    cU
    clo
    wcel
    @14
    @15
    wb
    @1
    cT
    hmoplin
    cU
    hmoplin
    vx
    cT
    cU
    lnopeq
    syl2an
    3bitrd
end
