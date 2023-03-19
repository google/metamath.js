include "csingle.mm"
include "cvv.mm"
include "wfn.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "wrel.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "cxp.mm"
include "cep.mm"
include "ctxp.mm"
include "cid.mm"
include "csymdif.mm"
include "crn.mm"
include "cdif.mm"
include "wss.mm"
include "difss.mm"
include "df-rel.mm"
include "mpbir.mm"
include "df-singleton.mm"
include "releqi.mm"
include "csn.mm"
include "vex.mm"
include "brsingle.mm"
include "eqtr3.mm"
include "syl2anb.mm"
include "ax-gen.mm"
include "gen2.mm"
include "dffun2.mm"
include "mpbir2an.mm"
include "wcel.mm"
include "eqv.mm"
include "wex.mm"
include "eqid.mm"
include "snex.mm"
include "breq2.mm"
include "spcev.mm"
include "ax-mp.mm"
include "eldm.mm"
include "mpgbir.mm"
include "df-fn.mm"

theorem fnsingle
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- Singleton Fn _V

  proof
    csingle
    cvv
    wfn
    csingle
    wfun
    #
    csingle
    cdm
    #
    cvv
    wceq
    #
    @0
    csingle
    wrel
    #
    vx
    cv
    #
    vy
    cv
    #
    csingle
    wbr
    #
    @4
    vz
    cv
    #
    csingle
    wbr
    #
    wa
    vy
    vz
    weq
    #
    wi
    #
    vz
    wal
    #
    vy
    wal
    vx
    wal
    @3
    cvv
    cvv
    cxp
    #
    cvv
    cep
    ctxp
    cid
    cvv
    ctxp
    csymdif
    crn
    #
    cdif
    #
    wrel
    #
    @15
    @14
    @12
    wss
    @12
    @13
    difss
    @14
    df-rel
    mpbir
    csingle
    @14
    df-singleton
    releqi
    mpbir
    @11
    vx
    vy
    @10
    vz
    @6
    @5
    @4
    csn
    #
    wceq
    @7
    @16
    wceq
    @9
    @8
    @4
    @5
    vx
    vex
    #
    vy
    vex
    brsingle
    @4
    @7
    @17
    vz
    vex
    brsingle
    @5
    @7
    @16
    eqtr3
    syl2anb
    ax-gen
    gen2
    vx
    vy
    vz
    csingle
    dffun2
    mpbir2an
    @2
    @4
    @1
    wcel
    #
    vx
    vx
    @1
    eqv
    @18
    @6
    vy
    wex
    #
    @4
    @16
    csingle
    wbr
    #
    @19
    @20
    @16
    @16
    wceq
    @16
    eqid
    @4
    @16
    @17
    @4
    snex
    #
    brsingle
    mpbir
    @6
    @20
    vy
    @16
    @21
    @5
    @16
    @4
    csingle
    breq2
    spcev
    ax-mp
    vy
    @4
    csingle
    @17
    eldm
    mpbir
    mpgbir
    csingle
    cvv
    df-fn
    mpbir2an
end
