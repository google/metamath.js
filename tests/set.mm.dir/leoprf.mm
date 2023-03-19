include "cho.mm"
include "wcel.mm"
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
include "wa.mm"
include "0le0.mm"
include "c0v.mm"
include "ch0o.mm"
include "wceq.mm"
include "wf.mm"
include "hmopf.mm"
include "hodid.mm"
include "syl.mm"
include "adantr.mm"
include "fveq1d.mm"
include "ho0val.mm"
include "adantl.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "hi01.mm"
include "eqtr2d.mm"
include "syl5breq.mm"
include "ralrimiva.mm"
include "wb.mm"
include "leop.mm"
include "anidms.mm"
include "mpbird.mm"

theorem leoprf
  let cT: class T
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
  let cU: class U


  assert |- ( T e. HrmOp -> T <_op T )

  proof
    cT
    cho
    wcel
    #
    cT
    cT
    cleo
    wbr
    #
    cc0
    vx
    cv
    #
    cT
    cT
    chod
    co
    #
    cfv
    #
    @2
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
    @0
    @6
    vx
    chil
    @0
    @2
    chil
    wcel
    #
    wa
    #
    cc0
    cc0
    @5
    cle
    0le0
    @9
    @5
    c0v
    @2
    csp
    co
    #
    cc0
    @9
    @4
    c0v
    @2
    csp
    @9
    @4
    @2
    ch0o
    cfv
    #
    c0v
    @9
    @2
    @3
    ch0o
    @0
    @3
    ch0o
    wceq
    #
    @8
    @0
    chil
    chil
    cT
    wf
    @12
    cT
    hmopf
    cT
    hodid
    syl
    adantr
    fveq1d
    @8
    @11
    c0v
    wceq
    @0
    @2
    ho0val
    adantl
    eqtrd
    oveq1d
    @8
    @10
    cc0
    wceq
    @0
    @2
    hi01
    adantl
    eqtr2d
    syl5breq
    ralrimiva
    @0
    @1
    @7
    wb
    vx
    cT
    cT
    leop
    anidms
    mpbird
end
