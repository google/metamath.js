include "crest.mm"
include "co.mm"
include "cpw.mm"
include "cv.mm"
include "wcel.mm"
include "wss.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "cvv.mm"
include "wa.mm"
include "wb.mm"
include "c0.mm"
include "n0i.mm"
include "cxp.mm"
include "wfn.mm"
include "cdm.mm"
include "restfn.mm"
include "fndm.mm"
include "ax-mp.mm"
include "ndmov.mm"
include "nsyl2.mm"
include "elrest.mm"
include "syl.mm"
include "ibi.mm"
include "inss2.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "rexlimivw.mm"
include "selpw.mm"
include "sylibr.mm"
include "ssriv.mm"

theorem restsspw
  let cA: class A
  let cJ: class J
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cV: class V


  assert |- ( J |`t A ) C_ ~P A

  proof
    vx
    cJ
    cA
    crest
    co
    #
    cA
    cpw
    #
    vx
    cv
    #
    @0
    wcel
    #
    @2
    cA
    wss
    #
    @2
    @1
    wcel
    @3
    @2
    vy
    cv
    #
    cA
    cin
    #
    wceq
    #
    vy
    cJ
    wrex
    #
    @4
    @3
    @8
    @3
    cJ
    cvv
    wcel
    cA
    cvv
    wcel
    wa
    #
    @3
    @8
    wb
    @3
    @0
    c0
    wceq
    @9
    @0
    @2
    n0i
    cJ
    cA
    cvv
    crest
    crest
    cvv
    cvv
    cxp
    #
    wfn
    crest
    cdm
    @10
    wceq
    restfn
    @10
    crest
    fndm
    ax-mp
    ndmov
    nsyl2
    vy
    @2
    cA
    cJ
    cvv
    cvv
    elrest
    syl
    ibi
    @7
    @4
    vy
    cJ
    @7
    @4
    @6
    cA
    wss
    @5
    cA
    inss2
    @2
    @6
    cA
    sseq1
    mpbiri
    rexlimivw
    syl
    vx
    cA
    selpw
    sylibr
    ssriv
end
