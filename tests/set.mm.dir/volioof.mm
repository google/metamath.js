include "cvol.mm"
include "cdm.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "cxr.mm"
include "cxp.mm"
include "cioo.mm"
include "ccom.mm"
include "volf.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "cr.mm"
include "cpw.mm"
include "ioof.mm"
include "ffn.mm"
include "ax-mp.mm"
include "c1st.mm"
include "c2nd.mm"
include "cop.mm"
include "wceq.mm"
include "df-ov.mm"
include "a1i.mm"
include "1st2nd2.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "eqtr2d.mm"
include "ioombl.mm"
include "syl6eqel.mm"
include "rgen.mm"
include "pm3.2i.mm"
include "ffnfv.mm"
include "mpbir.mm"
include "fco.mm"
include "mp2an.mm"

theorem volioof
  let vk: setvar k
  let vx: setvar x


  assert |- ( vol o. (,) ) : ( RR* X. RR* ) --> ( 0 [,] +oo )

  proof
    cvol
    cdm
    #
    cc0
    cpnf
    cicc
    co
    #
    cvol
    wf
    cxr
    cxr
    cxp
    #
    @0
    cioo
    wf
    #
    @2
    @1
    cvol
    cioo
    ccom
    wf
    volf
    @3
    cioo
    @2
    wfn
    #
    vx
    cv
    #
    cioo
    cfv
    #
    @0
    wcel
    #
    vx
    @2
    wral
    #
    wa
    @4
    @8
    @2
    cr
    cpw
    #
    cioo
    wf
    @4
    ioof
    @2
    @9
    cioo
    ffn
    ax-mp
    @7
    vx
    @2
    @5
    @2
    wcel
    #
    @6
    @5
    c1st
    cfv
    #
    @5
    c2nd
    cfv
    #
    cioo
    co
    #
    @0
    @10
    @13
    @11
    @12
    cop
    #
    cioo
    cfv
    #
    @6
    @13
    @15
    wceq
    @10
    @11
    @12
    cioo
    df-ov
    a1i
    @10
    @14
    @5
    cioo
    @10
    @5
    @14
    @5
    cxr
    cxr
    1st2nd2
    eqcomd
    fveq2d
    eqtr2d
    @11
    @12
    ioombl
    syl6eqel
    rgen
    pm3.2i
    vx
    @2
    @0
    cioo
    ffnfv
    mpbir
    @2
    @0
    @1
    cvol
    cioo
    fco
    mp2an
end
