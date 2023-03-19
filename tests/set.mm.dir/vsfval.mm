include "cnsb.mm"
include "cfv.mm"
include "cpv.mm"
include "cgs.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "ccom.mm"
include "df-vs.mm"
include "fveq1i.mm"
include "wf.mm"
include "c1st.mm"
include "wfo.mm"
include "fo1st.mm"
include "fof.mm"
include "ax-mp.mm"
include "fco.mm"
include "mp2an.mm"
include "df-va.mm"
include "feq1i.mm"
include "mpbir.mm"
include "fvco3.mm"
include "mpan.mm"
include "syl5eq.mm"
include "wn.mm"
include "c0.mm"
include "cdm.mm"
include "cgr.mm"
include "0ngrp.mm"
include "cv.mm"
include "crn.mm"
include "cgn.mm"
include "co.mm"
include "cmpt2.mm"
include "vex.mm"
include "rnex.mm"
include "mpt2ex.mm"
include "df-gdiv.mm"
include "dmmpti.mm"
include "eleq2i.mm"
include "mtbir.mm"
include "ndmfv.mm"
include "mp1i.mm"
include "fvprc.mm"
include "fveq2d.mm"
include "3eqtr4rd.mm"
include "pm2.61i.mm"
include "fveq2i.mm"
include "3eqtr4i.mm"

theorem vsfval
  let cU: class U
  let cG: class G
  let cM: class M
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  assume vsfval.2: |- G = ( +v ` U )
  assume vsfval.3: |- M = ( -v ` U )


  assert |- M = ( /g ` G )

  proof
    cU
    cnsb
    cfv
    #
    cU
    cpv
    cfv
    #
    cgs
    cfv
    #
    cM
    cG
    cgs
    cfv
    cU
    cvv
    wcel
    #
    @0
    @2
    wceq
    @3
    @0
    cU
    cgs
    cpv
    ccom
    #
    cfv
    #
    @2
    cU
    cnsb
    @4
    df-vs
    fveq1i
    cvv
    cvv
    cpv
    wf
    #
    @3
    @5
    @2
    wceq
    @6
    cvv
    cvv
    c1st
    c1st
    ccom
    #
    wf
    #
    cvv
    cvv
    c1st
    wf
    #
    @9
    @8
    cvv
    cvv
    c1st
    wfo
    @9
    fo1st
    cvv
    cvv
    c1st
    fof
    ax-mp
    #
    @10
    cvv
    cvv
    cvv
    c1st
    c1st
    fco
    mp2an
    cvv
    cvv
    cpv
    @7
    df-va
    feq1i
    mpbir
    cvv
    cvv
    cU
    cgs
    cpv
    fvco3
    mpan
    syl5eq
    @3
    wn
    #
    c0
    cgs
    cfv
    #
    c0
    @2
    @0
    c0
    cgs
    cdm
    #
    wcel
    #
    wn
    @12
    c0
    wceq
    @11
    @14
    c0
    cgr
    wcel
    0ngrp
    @13
    cgr
    c0
    vg
    cgr
    vx
    vy
    vg
    cv
    #
    crn
    #
    @16
    vx
    cv
    vy
    cv
    @15
    cgn
    cfv
    cfv
    @15
    co
    #
    cmpt2
    cgs
    vx
    vy
    @16
    @16
    @17
    @15
    vg
    vex
    rnex
    #
    @18
    mpt2ex
    vx
    vy
    vg
    df-gdiv
    dmmpti
    eleq2i
    mtbir
    c0
    cgs
    ndmfv
    mp1i
    @11
    @1
    c0
    cgs
    cU
    cpv
    fvprc
    fveq2d
    cU
    cnsb
    fvprc
    3eqtr4rd
    pm2.61i
    vsfval.3
    cG
    @1
    cgs
    vsfval.2
    fveq2i
    3eqtr4i
end
