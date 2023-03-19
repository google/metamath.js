include "c0.mm"
include "wne.mm"
include "cxp.mm"
include "c1st.mm"
include "cres.mm"
include "wf.mm"
include "crn.mm"
include "wceq.mm"
include "wa.mm"
include "wfo.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "wi.mm"
include "n0.mm"
include "cop.mm"
include "opelxp.mm"
include "cfv.mm"
include "fvres.mm"
include "vex.mm"
include "op1st.mm"
include "syl6req.mm"
include "wfn.mm"
include "f1stres.mm"
include "ffn.mm"
include "ax-mp.mm"
include "fnfvelrn.mm"
include "mpan.mm"
include "eqeltrd.mm"
include "sylbir.mm"
include "expcom.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "ssrdv.mm"
include "frn.mm"
include "jctil.mm"
include "eqss.mm"
include "sylibr.mm"
include "dffo2.mm"

theorem fo1stres
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( B =/= (/) -> ( 1st |` ( A X. B ) ) : ( A X. B ) -onto-> A )

  proof
    cB
    c0
    wne
    #
    cA
    cB
    cxp
    #
    cA
    c1st
    @1
    cres
    #
    wf
    #
    @2
    crn
    #
    cA
    wceq
    #
    wa
    @1
    cA
    @2
    wfo
    @0
    @5
    @3
    @0
    @4
    cA
    wss
    #
    cA
    @4
    wss
    #
    wa
    @5
    @0
    @7
    @6
    @0
    vx
    cA
    @4
    @0
    vy
    cv
    #
    cB
    wcel
    #
    vy
    wex
    vx
    cv
    #
    cA
    wcel
    #
    @10
    @4
    wcel
    #
    wi
    #
    vy
    cB
    n0
    @9
    @13
    vy
    @11
    @9
    @12
    @11
    @9
    wa
    @10
    @8
    cop
    #
    @1
    wcel
    #
    @12
    @10
    @8
    cA
    cB
    opelxp
    @15
    @10
    @14
    @2
    cfv
    #
    @4
    @15
    @16
    @14
    c1st
    cfv
    @10
    @14
    @1
    c1st
    fvres
    @10
    @8
    vx
    vex
    vy
    vex
    op1st
    syl6req
    @2
    @1
    wfn
    #
    @15
    @16
    @4
    wcel
    @3
    @17
    cA
    cB
    f1stres
    #
    @1
    cA
    @2
    ffn
    ax-mp
    @1
    @14
    @2
    fnfvelrn
    mpan
    eqeltrd
    sylbir
    expcom
    exlimiv
    sylbi
    ssrdv
    @3
    @6
    @18
    @1
    cA
    @2
    frn
    ax-mp
    jctil
    @4
    cA
    eqss
    sylibr
    @18
    jctil
    @1
    cA
    @2
    dffo2
    sylibr
end
