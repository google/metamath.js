include "c1o.mm"
include "cfinxp.mm"
include "cv.mm"
include "wcel.mm"
include "com.mm"
include "c0.mm"
include "cvv.mm"
include "wceq.mm"
include "wa.mm"
include "cxp.mm"
include "cuni.mm"
include "c1st.mm"
include "cfv.mm"
include "cop.mm"
include "cif.mm"
include "cmpt2.mm"
include "crdg.mm"
include "1onn.mm"
include "a1i.mm"
include "finxpreclem1.mm"
include "con0.mm"
include "wne.mm"
include "wlim.mm"
include "wn.mm"
include "1on.mm"
include "1n0.mm"
include "nnlim.mm"
include "ax-mp.mm"
include "rdgsucuni.mm"
include "mp3an.mm"
include "csuc.mm"
include "df-1o.mm"
include "unieqi.mm"
include "0elon.mm"
include "onunisuci.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "opex.mm"
include "rdg0.mm"
include "syl6eqr.mm"
include "df-finxp.mm"
include "abeq2i.mm"
include "sylanbrc.mm"
include "mpbiran.mm"
include "vex.mm"
include "eqcomi.mm"
include "finxpreclem2.mm"
include "neqned.mm"
include "necomd.mm"
include "syl5eqner.mm"
include "neneqd.mm"
include "mpan.mm"
include "con4i.mm"
include "sylbi.mm"
include "impbii.mm"
include "eqriv.mm"

theorem finxp1o
  let cU: class U
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y


  assert |- ( U ^^ 1o ) = U

  proof
    cU
    cU
    c1o
    cfinxp
    #
    vy
    cU
    @0
    vy
    cv
    #
    cU
    wcel
    #
    @1
    @0
    wcel
    #
    @2
    c1o
    com
    wcel
    #
    c0
    c1o
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
    c1o
    @1
    cop
    #
    crdg
    #
    cfv
    #
    wceq
    #
    @3
    @4
    @2
    1onn
    a1i
    @2
    c0
    @8
    @7
    cfv
    #
    @10
    vx
    cU
    vn
    @1
    finxpreclem1
    @10
    c1o
    cuni
    #
    @9
    cfv
    #
    @7
    cfv
    #
    @12
    c1o
    con0
    wcel
    c1o
    c0
    wne
    c1o
    wlim
    wn
    #
    @10
    @15
    wceq
    1on
    1n0
    @4
    @16
    1onn
    c1o
    nnlim
    ax-mp
    c1o
    @7
    @8
    rdgsucuni
    mp3an
    @14
    @8
    @7
    @14
    c0
    @9
    cfv
    @8
    @13
    c0
    @9
    @13
    c0
    csuc
    #
    cuni
    c0
    c1o
    @17
    df-1o
    unieqi
    c0
    0elon
    onunisuci
    eqtri
    fveq2i
    @8
    @7
    c1o
    @1
    opex
    rdg0
    eqtri
    fveq2i
    eqtri
    #
    syl6eqr
    @4
    @11
    wa
    vy
    @0
    vx
    vy
    cU
    vn
    c1o
    df-finxp
    abeq2i
    #
    sylanbrc
    @3
    @11
    @2
    @3
    @4
    @11
    1onn
    @19
    mpbiran
    @2
    @11
    @1
    cvv
    wcel
    #
    @2
    wn
    #
    @11
    wn
    vy
    vex
    @20
    @21
    wa
    #
    c0
    @10
    @22
    @10
    c0
    @22
    @10
    @12
    c0
    @10
    @12
    @18
    eqcomi
    @22
    c0
    @12
    @22
    c0
    @12
    vx
    cU
    vn
    @1
    finxpreclem2
    neqned
    necomd
    syl5eqner
    necomd
    neneqd
    mpan
    con4i
    sylbi
    impbii
    eqriv
    eqcomi
end
