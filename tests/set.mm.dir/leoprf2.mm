include "chil.mm"
include "wf.mm"
include "cleo.mm"
include "wbr.mm"
include "chod.mm"
include "co.mm"
include "cho.mm"
include "wcel.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "cle.mm"
include "wral.mm"
include "ch0o.mm"
include "hodid.mm"
include "0hmop.mm"
include "syl6eqel.mm"
include "wa.mm"
include "0le0.mm"
include "c0v.mm"
include "wceq.mm"
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
include "cvv.mm"
include "wb.mm"
include "ax-hilex.mm"
include "fex.mm"
include "mpan2.mm"
include "leopg.mm"
include "syl2anc.mm"
include "mpbir2and.mm"

theorem leoprf2
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


  assert |- ( T : ~H --> ~H -> T <_op T )

  proof
    chil
    chil
    cT
    wf
    #
    cT
    cT
    cleo
    wbr
    #
    cT
    cT
    chod
    co
    #
    cho
    wcel
    #
    cc0
    vx
    cv
    #
    @2
    cfv
    #
    @4
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
    @2
    ch0o
    cho
    cT
    hodid
    #
    0hmop
    syl6eqel
    @0
    @7
    vx
    chil
    @0
    @4
    chil
    wcel
    #
    wa
    #
    cc0
    cc0
    @6
    cle
    0le0
    @11
    @6
    c0v
    @4
    csp
    co
    #
    cc0
    @11
    @5
    c0v
    @4
    csp
    @11
    @5
    @4
    ch0o
    cfv
    #
    c0v
    @11
    @4
    @2
    ch0o
    @0
    @2
    ch0o
    wceq
    @10
    @9
    adantr
    fveq1d
    @10
    @13
    c0v
    wceq
    @0
    @4
    ho0val
    adantl
    eqtrd
    oveq1d
    @10
    @12
    cc0
    wceq
    @0
    @4
    hi01
    adantl
    eqtr2d
    syl5breq
    ralrimiva
    @0
    cT
    cvv
    wcel
    #
    @14
    @1
    @3
    @8
    wa
    wb
    @0
    chil
    cvv
    wcel
    @14
    ax-hilex
    chil
    chil
    cvv
    cT
    fex
    mpan2
    #
    @15
    vx
    cvv
    cvv
    cT
    cT
    leopg
    syl2anc
    mpbir2and
end
