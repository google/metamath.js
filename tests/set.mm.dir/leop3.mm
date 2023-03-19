include "cho.mm"
include "wcel.mm"
include "wa.mm"
include "cleo.mm"
include "wbr.mm"
include "cc0.mm"
include "cv.mm"
include "chod.mm"
include "co.mm"
include "cfv.mm"
include "csp.mm"
include "cle.mm"
include "chil.mm"
include "wral.mm"
include "ch0o.mm"
include "leop.mm"
include "wb.mm"
include "0hmop.mm"
include "hmopd.mm"
include "ancoms.mm"
include "leop2.mm"
include "sylancr.mm"
include "c0v.mm"
include "ho0val.mm"
include "oveq1d.mm"
include "hi01.mm"
include "eqtrd.mm"
include "breq1d.mm"
include "ralbiia.mm"
include "syl6rbb.mm"
include "bitrd.mm"

theorem leop3
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


  assert |- ( ( T e. HrmOp /\ U e. HrmOp ) -> ( T <_op U <-> 0hop <_op ( U -op T ) ) )

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
    cc0
    vx
    cv
    #
    cU
    cT
    chod
    co
    #
    cfv
    @3
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
    ch0o
    @4
    cleo
    wbr
    #
    vx
    cT
    cU
    leop
    @2
    @8
    @3
    ch0o
    cfv
    #
    @3
    csp
    co
    #
    @5
    cle
    wbr
    #
    vx
    chil
    wral
    #
    @7
    @2
    ch0o
    cho
    wcel
    @4
    cho
    wcel
    #
    @8
    @12
    wb
    0hmop
    @1
    @0
    @13
    cU
    cT
    hmopd
    ancoms
    vx
    ch0o
    @4
    leop2
    sylancr
    @11
    @6
    vx
    chil
    @3
    chil
    wcel
    #
    @10
    cc0
    @5
    cle
    @14
    @10
    c0v
    @3
    csp
    co
    cc0
    @14
    @9
    c0v
    @3
    csp
    @3
    ho0val
    oveq1d
    @3
    hi01
    eqtrd
    breq1d
    ralbiia
    syl6rbb
    bitrd
end
