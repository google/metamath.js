include "chil.mm"
include "c0h.mm"
include "wceq.mm"
include "wf.mm"
include "wa.mm"
include "cnop.mm"
include "cfv.mm"
include "ch0o.mm"
include "cc0.mm"
include "c0v.mm"
include "csn.mm"
include "wb.mm"
include "df-ch0.mm"
include "eqeq2i.mm"
include "feq3.mm"
include "sylbi.mm"
include "cxp.mm"
include "ax-hv0cl.mm"
include "elexi.mm"
include "fconst2.mm"
include "df0op2.mm"
include "xpeq2i.mm"
include "eqtri.mm"
include "bitr4i.mm"
include "syl6bb.mm"
include "biimpa.mm"
include "fveq2d.mm"
include "nmop0.mm"
include "syl6eq.mm"

theorem nmop0h
  let cT: class T


  assert |- ( ( ~H = 0H /\ T : ~H --> ~H ) -> ( normop ` T ) = 0 )

  proof
    chil
    c0h
    wceq
    #
    chil
    chil
    cT
    wf
    #
    wa
    #
    cT
    cnop
    cfv
    ch0o
    cnop
    cfv
    cc0
    @2
    cT
    ch0o
    cnop
    @0
    @1
    cT
    ch0o
    wceq
    #
    @0
    @1
    chil
    c0v
    csn
    #
    cT
    wf
    #
    @3
    @0
    chil
    @4
    wceq
    @1
    @5
    wb
    c0h
    @4
    chil
    df-ch0
    eqeq2i
    chil
    @4
    chil
    cT
    feq3
    sylbi
    @5
    cT
    chil
    @4
    cxp
    #
    wceq
    @3
    chil
    c0v
    cT
    c0v
    chil
    ax-hv0cl
    elexi
    fconst2
    ch0o
    @6
    cT
    ch0o
    chil
    c0h
    cxp
    @6
    df0op2
    c0h
    @4
    chil
    df-ch0
    xpeq2i
    eqtri
    eqeq2i
    bitr4i
    syl6bb
    biimpa
    fveq2d
    nmop0
    syl6eq
end
