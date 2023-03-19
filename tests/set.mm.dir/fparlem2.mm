include "c2nd.mm"
include "cvv.mm"
include "cxp.mm"
include "cres.mm"
include "ccnv.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "c1st.mm"
include "fvres.mm"
include "eqeq1d.mm"
include "vex.mm"
include "elsn2.mm"
include "fvex.mm"
include "biantrur.mm"
include "bitr3i.mm"
include "syl6bb.mm"
include "pm5.32i.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "f2ndres.mm"
include "ffn.mm"
include "fniniseg.mm"
include "mp2b.mm"
include "elxp7.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem fparlem2
  let vy: setvar y
  let cA: class A
  let vx: setvar x
  let cB: class B
  let cF: class F
  let cG: class G


  assert |- ( `' ( 2nd |` ( _V X. _V ) ) " { y } ) = ( _V X. { y } )

  proof
    vx
    c2nd
    cvv
    cvv
    cxp
    #
    cres
    #
    ccnv
    vy
    cv
    #
    csn
    #
    cima
    #
    cvv
    @3
    cxp
    #
    vx
    cv
    #
    @0
    wcel
    #
    @6
    @1
    cfv
    #
    @2
    wceq
    #
    wa
    #
    @7
    @6
    c1st
    cfv
    cvv
    wcel
    #
    @6
    c2nd
    cfv
    #
    @3
    wcel
    #
    wa
    #
    wa
    @6
    @4
    wcel
    #
    @6
    @5
    wcel
    @7
    @9
    @14
    @7
    @9
    @12
    @2
    wceq
    #
    @14
    @7
    @8
    @12
    @2
    @6
    @0
    c2nd
    fvres
    eqeq1d
    @16
    @13
    @14
    @12
    @2
    vy
    vex
    elsn2
    @11
    @13
    @6
    c1st
    fvex
    biantrur
    bitr3i
    syl6bb
    pm5.32i
    @0
    cvv
    @1
    wf
    @1
    @0
    wfn
    @15
    @10
    wb
    cvv
    cvv
    f2ndres
    @0
    cvv
    @1
    ffn
    @0
    @2
    @6
    @1
    fniniseg
    mp2b
    @6
    cvv
    @3
    elxp7
    3bitr4i
    eqriv
end
