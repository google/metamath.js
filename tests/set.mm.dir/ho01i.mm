include "chil.mm"
include "c0v.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "ch0o.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "wfn.mm"
include "wb.mm"
include "wf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "ax-hv0cl.mm"
include "elexi.mm"
include "fconst.mm"
include "eqfnfv.mm"
include "mp2an.mm"
include "c0h.mm"
include "df0op2.mm"
include "df-ch0.mm"
include "xpeq2i.mm"
include "eqtri.mm"
include "eqeq2i.mm"
include "wcel.mm"
include "ffvelrni.mm"
include "hial0.mm"
include "syl.mm"
include "fvconst2.mm"
include "eqeq2d.mm"
include "bitr4d.mm"
include "ralbiia.mm"
include "3bitr4ri.mm"

theorem ho01i
  let vx: setvar x
  let vy: setvar y
  let cT: class T
  assume ho0.1: |- T : ~H --> ~H

  disjoint x y
  disjoint T x
  disjoint T y
  assert |- ( A. x e. ~H A. y e. ~H ( ( T ` x ) .ih y ) = 0 <-> T = 0hop )

  proof
    cT
    chil
    c0v
    csn
    #
    cxp
    #
    wceq
    #
    vx
    cv
    #
    cT
    cfv
    #
    @3
    @1
    cfv
    #
    wceq
    #
    vx
    chil
    wral
    #
    cT
    ch0o
    wceq
    @4
    vy
    cv
    csp
    co
    cc0
    wceq
    vy
    chil
    wral
    #
    vx
    chil
    wral
    cT
    chil
    wfn
    #
    @1
    chil
    wfn
    #
    @2
    @7
    wb
    chil
    chil
    cT
    wf
    @9
    ho0.1
    chil
    chil
    cT
    ffn
    ax-mp
    chil
    @0
    @1
    wf
    @10
    chil
    c0v
    c0v
    chil
    ax-hv0cl
    elexi
    #
    fconst
    chil
    @0
    @1
    ffn
    ax-mp
    vx
    chil
    cT
    @1
    eqfnfv
    mp2an
    ch0o
    @1
    cT
    ch0o
    chil
    c0h
    cxp
    @1
    df0op2
    c0h
    @0
    chil
    df-ch0
    xpeq2i
    eqtri
    eqeq2i
    @8
    @6
    vx
    chil
    @3
    chil
    wcel
    #
    @8
    @4
    c0v
    wceq
    #
    @6
    @12
    @4
    chil
    wcel
    @8
    @13
    wb
    chil
    chil
    @3
    cT
    ho0.1
    ffvelrni
    vy
    @4
    hial0
    syl
    @12
    @5
    c0v
    @4
    chil
    c0v
    @3
    @11
    fvconst2
    eqeq2d
    bitr4d
    ralbiia
    3bitr4ri
end
