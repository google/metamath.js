include "c1st.mm"
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
include "c2nd.mm"
include "fvres.mm"
include "eqeq1d.mm"
include "vex.mm"
include "elsn2.mm"
include "fvex.mm"
include "biantru.mm"
include "bitr3i.mm"
include "syl6bb.mm"
include "pm5.32i.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "f1stres.mm"
include "ffn.mm"
include "fniniseg.mm"
include "mp2b.mm"
include "elxp7.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem fparlem1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let cF: class F
  let cG: class G


  assert |- ( `' ( 1st |` ( _V X. _V ) ) " { x } ) = ( { x } X. _V )

  proof
    vy
    c1st
    cvv
    cvv
    cxp
    #
    cres
    #
    ccnv
    vx
    cv
    #
    csn
    #
    cima
    #
    @3
    cvv
    cxp
    #
    vy
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
    #
    @3
    wcel
    #
    @6
    c2nd
    cfv
    cvv
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
    @11
    @2
    wceq
    #
    @14
    @7
    @8
    @11
    @2
    @6
    @0
    c1st
    fvres
    eqeq1d
    @16
    @12
    @14
    @11
    @2
    vx
    vex
    elsn2
    @13
    @12
    @6
    c2nd
    fvex
    biantru
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
    f1stres
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
    @3
    cvv
    elxp7
    3bitr4i
    eqriv
end
