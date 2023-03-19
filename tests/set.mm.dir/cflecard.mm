include "con0.mm"
include "wcel.mm"
include "ccf.mm"
include "cfv.mm"
include "ccrd.mm"
include "wss.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "cint.mm"
include "cfval.mm"
include "csn.mm"
include "df-sn.mm"
include "ssid.mm"
include "sseq2.mm"
include "rspcev.mm"
include "mpan2.mm"
include "rgen.mm"
include "pm3.2i.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "sseq1.mm"
include "rexeq.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "mpan2i.mm"
include "ss2abdv.mm"
include "syl5eqss.mm"
include "intss.mm"
include "syl.mm"
include "fvex.mm"
include "intsn.mm"
include "syl6sseq.mm"
include "eqsstrd.mm"
include "wn.mm"
include "c0.mm"
include "cdm.mm"
include "cff.mm"
include "fdmi.mm"
include "eleq2i.mm"
include "ndmfv.mm"
include "sylnbir.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "pm2.61i.mm"

theorem cflecard
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v


  assert |- ( cf ` A ) C_ ( card ` A )

  proof
    cA
    con0
    wcel
    #
    cA
    ccf
    cfv
    #
    cA
    ccrd
    cfv
    #
    wss
    @0
    @1
    vx
    cv
    #
    vy
    cv
    #
    ccrd
    cfv
    #
    wceq
    #
    @4
    cA
    wss
    #
    vz
    cv
    #
    vw
    cv
    #
    wss
    #
    vw
    @4
    wrex
    #
    vz
    cA
    wral
    #
    wa
    #
    wa
    #
    vy
    wex
    #
    vx
    cab
    #
    cint
    #
    @2
    vx
    vy
    vz
    vw
    cA
    cfval
    @0
    @17
    @2
    csn
    #
    cint
    #
    @2
    @0
    @18
    @16
    wss
    @17
    @19
    wss
    @0
    @18
    @3
    @2
    wceq
    #
    vx
    cab
    @16
    vx
    @2
    df-sn
    @0
    @20
    @15
    vx
    @0
    @20
    cA
    cA
    wss
    #
    @10
    vw
    cA
    wrex
    #
    vz
    cA
    wral
    #
    wa
    #
    @15
    @21
    @23
    cA
    ssid
    @22
    vz
    cA
    @8
    cA
    wcel
    @8
    @8
    wss
    #
    @22
    @8
    ssid
    @10
    @25
    vw
    @8
    cA
    @9
    @8
    @8
    sseq2
    rspcev
    mpan2
    rgen
    pm3.2i
    @14
    @20
    @24
    wa
    vy
    cA
    con0
    @4
    cA
    wceq
    #
    @6
    @20
    @13
    @24
    @26
    @5
    @2
    @3
    @4
    cA
    ccrd
    fveq2
    eqeq2d
    @26
    @7
    @21
    @12
    @23
    @4
    cA
    cA
    sseq1
    @26
    @11
    @22
    vz
    cA
    @10
    vw
    @4
    cA
    rexeq
    ralbidv
    anbi12d
    anbi12d
    spcegv
    mpan2i
    ss2abdv
    syl5eqss
    @18
    @16
    intss
    syl
    @2
    cA
    ccrd
    fvex
    intsn
    syl6sseq
    eqsstrd
    @0
    wn
    @1
    c0
    @2
    @0
    cA
    ccf
    cdm
    #
    wcel
    @1
    c0
    wceq
    @27
    con0
    cA
    con0
    con0
    ccf
    cff
    fdmi
    eleq2i
    cA
    ccf
    ndmfv
    sylnbir
    @2
    0ss
    syl6eqss
    pm2.61i
end
