include "c0.mm"
include "cfinxp.mm"
include "cv.mm"
include "wcel.mm"
include "cop.mm"
include "wceq.mm"
include "0ex.mm"
include "vex.mm"
include "opnzi.mm"
include "nesymi.mm"
include "com.mm"
include "cvv.mm"
include "c1o.mm"
include "wa.mm"
include "cxp.mm"
include "cuni.mm"
include "c1st.mm"
include "cfv.mm"
include "cif.mm"
include "cmpt2.mm"
include "crdg.mm"
include "peano1.mm"
include "df-finxp.mm"
include "abeq2i.mm"
include "mpbiran.mm"
include "opex.mm"
include "rdg0.mm"
include "eqeq2i.mm"
include "bitri.mm"
include "mtbir.mm"
include "nel0.mm"

theorem finxp0
  let cU: class U
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y


  assert |- ( U ^^ (/) ) = (/)

  proof
    vy
    cU
    c0
    cfinxp
    #
    vy
    cv
    #
    @0
    wcel
    #
    c0
    c0
    @1
    cop
    #
    wceq
    #
    @3
    c0
    c0
    @1
    0ex
    vy
    vex
    opnzi
    nesymi
    @2
    c0
    c0
    vn
    vx
    com
    cvv
    vn
    cv
    #
    c1o
    wceq
    vx
    cv
    #
    cU
    wcel
    wa
    c0
    @6
    cvv
    cU
    cxp
    wcel
    @5
    cuni
    @6
    c1st
    cfv
    cop
    @5
    @6
    cop
    cif
    cif
    cmpt2
    #
    @3
    crdg
    cfv
    #
    wceq
    #
    @4
    @2
    c0
    com
    wcel
    #
    @9
    peano1
    @10
    @9
    wa
    vy
    @0
    vx
    vy
    cU
    vn
    c0
    df-finxp
    abeq2i
    mpbiran
    @8
    @3
    c0
    @3
    @7
    c0
    @1
    opex
    rdg0
    eqeq2i
    bitri
    mtbir
    nel0
end
