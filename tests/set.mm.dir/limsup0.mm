include "c0.mm"
include "clsp.mm"
include "cfv.mm"
include "cr.mm"
include "cv.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cxr.mm"
include "cin.mm"
include "clt.mm"
include "csup.mm"
include "cmpt.mm"
include "crn.mm"
include "cinf.mm"
include "cmnf.mm"
include "csn.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "0ex.mm"
include "eqid.mm"
include "limsupval.mm"
include "ax-mp.mm"
include "wtru.mm"
include "0ima.mm"
include "ineq1i.mm"
include "0in.mm"
include "eqtri.mm"
include "supeq1i.mm"
include "xrsup0.mm"
include "mpteq2i.mm"
include "wa.mm"
include "mnfxr.mm"
include "a1i.mm"
include "wne.mm"
include "ren0.mm"
include "rnmptc.mm"
include "trud.mm"
include "infeq1i.mm"
include "wor.mm"
include "xrltso.mm"
include "infsn.mm"
include "mp2an.mm"
include "3eqtri.mm"

theorem limsup0
  let vx: setvar x


  assert |- ( limsup ` (/) ) = -oo

  proof
    c0
    clsp
    cfv
    #
    vx
    cr
    c0
    vx
    cv
    #
    cpnf
    cico
    co
    #
    cima
    #
    cxr
    cin
    #
    cxr
    clt
    csup
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    cinf
    #
    cmnf
    csn
    #
    cxr
    clt
    cinf
    #
    cmnf
    c0
    cvv
    wcel
    @0
    @8
    wceq
    0ex
    vx
    c0
    @6
    cvv
    @6
    eqid
    limsupval
    ax-mp
    cxr
    @7
    @9
    clt
    @7
    @9
    wceq
    wtru
    vx
    cr
    cmnf
    cxr
    @6
    vx
    cr
    @5
    cmnf
    @5
    c0
    cxr
    clt
    csup
    cmnf
    cxr
    @4
    c0
    clt
    @4
    c0
    cxr
    cin
    c0
    @3
    c0
    cxr
    @2
    0ima
    ineq1i
    cxr
    0in
    eqtri
    supeq1i
    xrsup0
    eqtri
    mpteq2i
    cmnf
    cxr
    wcel
    #
    wtru
    @1
    cr
    wcel
    wa
    mnfxr
    a1i
    cr
    c0
    wne
    wtru
    ren0
    a1i
    rnmptc
    trud
    infeq1i
    cxr
    clt
    wor
    @11
    @10
    cmnf
    wceq
    xrltso
    mnfxr
    cxr
    cmnf
    clt
    infsn
    mp2an
    3eqtri
end
