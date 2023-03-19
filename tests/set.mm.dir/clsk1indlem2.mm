include "cv.mm"
include "cfv.mm"
include "wss.mm"
include "c3o.mm"
include "cpw.mm"
include "wcel.mm"
include "c0.mm"
include "csn.mm"
include "wceq.mm"
include "c1o.mm"
include "cpr.mm"
include "cif.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "id.mm"
include "snsspr1.mm"
include "syl6eqss.mm"
include "ancli.mm"
include "con3i.mm"
include "ssid.mm"
include "jctir.mm"
include "orri.mm"
include "a1i.mm"
include "sseq2.mm"
include "elimif.mm"
include "sylibr.mm"
include "weq.mm"
include "eqeq1.mm"
include "ifbieq2d.mm"
include "prex.mm"
include "vex.mm"
include "ifex.mm"
include "fvmpt.mm"
include "sseqtr4d.mm"
include "rgen.mm"

theorem clsk1indlem2
  let cK: class K
  let vs: setvar s
  let vr: setvar r
  assume clsk1indlem.k: |- K = ( r e. ~P 3o |-> if ( r = { (/) } , { (/) , 1o } , r ) )

  disjoint r s
  assert |- A. s e. ~P 3o s C_ ( K ` s )

  proof
    vs
    cv
    #
    @0
    cK
    cfv
    #
    wss
    vs
    c3o
    cpw
    #
    @0
    @2
    wcel
    #
    @0
    @0
    c0
    csn
    #
    wceq
    #
    c0
    c1o
    cpr
    #
    @0
    cif
    #
    @1
    @3
    @5
    @0
    @6
    wss
    #
    wa
    #
    @5
    wn
    #
    @0
    @0
    wss
    #
    wa
    #
    wo
    #
    @0
    @7
    wss
    #
    @13
    @3
    @9
    @12
    @9
    wn
    @10
    @11
    @5
    @9
    @5
    @8
    @5
    @0
    @4
    @6
    @5
    id
    c0
    c1o
    snsspr1
    syl6eqss
    ancli
    con3i
    @0
    ssid
    jctir
    orri
    a1i
    @5
    @14
    @8
    @11
    @6
    @0
    @7
    @6
    @0
    sseq2
    @7
    @0
    @0
    sseq2
    elimif
    sylibr
    vr
    @0
    vr
    cv
    #
    @4
    wceq
    #
    @6
    @15
    cif
    @7
    @2
    cK
    vr
    vs
    weq
    #
    @16
    @5
    @15
    @0
    @6
    @15
    @0
    @4
    eqeq1
    @17
    id
    ifbieq2d
    clsk1indlem.k
    @5
    @6
    @0
    c0
    c1o
    prex
    vs
    vex
    ifex
    fvmpt
    sseqtr4d
    rgen
end
