include "cpm.mm"
include "co.mm"
include "cxp.mm"
include "cpw.mm"
include "cv.mm"
include "wcel.mm"
include "wss.mm"
include "wfun.mm"
include "wa.mm"
include "cvv.mm"
include "wb.mm"
include "c0.mm"
include "wceq.mm"
include "n0i.mm"
include "wfn.mm"
include "cdm.mm"
include "fnpm.mm"
include "fndm.mm"
include "ax-mp.mm"
include "ndmov.mm"
include "nsyl2.mm"
include "elpmg.mm"
include "syl.mm"
include "ibi.mm"
include "simprd.mm"
include "selpw.mm"
include "sylibr.mm"
include "ssriv.mm"

theorem pmsspw
  let cA: class A
  let cB: class B
  let vf: setvar f


  assert |- ( A ^pm B ) C_ ~P ( B X. A )

  proof
    vf
    cA
    cB
    cpm
    co
    #
    cB
    cA
    cxp
    #
    cpw
    #
    vf
    cv
    #
    @0
    wcel
    #
    @3
    @1
    wss
    #
    @3
    @2
    wcel
    @4
    @3
    wfun
    #
    @5
    @4
    @6
    @5
    wa
    #
    @4
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    wa
    #
    @4
    @7
    wb
    @4
    @0
    c0
    wceq
    @8
    @0
    @3
    n0i
    cA
    cB
    cvv
    cpm
    cpm
    cvv
    cvv
    cxp
    #
    wfn
    cpm
    cdm
    @9
    wceq
    fnpm
    @9
    cpm
    fndm
    ax-mp
    ndmov
    nsyl2
    cA
    cB
    @3
    cvv
    cvv
    elpmg
    syl
    ibi
    simprd
    vf
    @1
    selpw
    sylibr
    ssriv
end
