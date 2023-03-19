include "ch0o.mm"
include "chil.mm"
include "c0v.mm"
include "csn.mm"
include "cxp.mm"
include "c0h.mm"
include "wf.mm"
include "wceq.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "ho0f.mm"
include "ffn.mm"
include "ax-mp.mm"
include "ho0val.mm"
include "rgen.mm"
include "fconstfv.mm"
include "mpbir2an.mm"
include "ax-hv0cl.mm"
include "elexi.mm"
include "fconst2.mm"
include "mpbi.mm"
include "df-ch0.mm"
include "xpeq2i.mm"
include "eqtr4i.mm"

theorem df0op2
  let vx: setvar x


  assert |- 0hop = ( ~H X. 0H )

  proof
    ch0o
    chil
    c0v
    csn
    #
    cxp
    #
    chil
    c0h
    cxp
    chil
    @0
    ch0o
    wf
    #
    ch0o
    @1
    wceq
    @2
    ch0o
    chil
    wfn
    #
    vx
    cv
    #
    ch0o
    cfv
    c0v
    wceq
    #
    vx
    chil
    wral
    chil
    chil
    ch0o
    wf
    @3
    ho0f
    chil
    chil
    ch0o
    ffn
    ax-mp
    @5
    vx
    chil
    @4
    ho0val
    rgen
    vx
    chil
    c0v
    ch0o
    fconstfv
    mpbir2an
    chil
    c0v
    ch0o
    c0v
    chil
    ax-hv0cl
    elexi
    fconst2
    mpbi
    c0h
    @0
    chil
    df-ch0
    xpeq2i
    eqtr4i
end
