include "wcel.mm"
include "weq.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wo.mm"
include "wral.mm"
include "wa.mm"
include "ctb.mm"
include "cpw.mm"
include "cuni.mm"
include "wss.mm"
include "id.mm"
include "pwidg.mm"
include "elind.mm"
include "elssuni.mm"
include "syl.mm"
include "inidm.mm"
include "ineq2.mm"
include "syl5eqr.mm"
include "pweqd.mm"
include "ineq2d.mm"
include "unieqd.mm"
include "sseq12d.mm"
include "syl5ibcom.mm"
include "wi.mm"
include "0ss.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "a1i.mm"
include "jaod.mm"
include "ralimdv.mm"
include "ralimia.mm"
include "adantl.mm"
include "wb.mm"
include "isbasisg.mm"
include "adantr.mm"
include "mpbird.mm"

theorem baspartn
  let vx: setvar x
  let vy: setvar y
  let cP: class P
  let cV: class V

  disjoint P x
  disjoint P y
  disjoint x y
  assert |- ( ( P e. V /\ A. x e. P A. y e. P ( x = y \/ ( x i^i y ) = (/) ) ) -> P e. TopBases )

  proof
    cP
    cV
    wcel
    #
    vx
    vy
    weq
    #
    vx
    cv
    #
    vy
    cv
    #
    cin
    #
    c0
    wceq
    #
    wo
    #
    vy
    cP
    wral
    #
    vx
    cP
    wral
    #
    wa
    cP
    ctb
    wcel
    #
    @4
    cP
    @4
    cpw
    #
    cin
    #
    cuni
    #
    wss
    #
    vy
    cP
    wral
    #
    vx
    cP
    wral
    #
    @8
    @15
    @0
    @7
    @14
    vx
    cP
    @2
    cP
    wcel
    #
    @6
    @13
    vy
    cP
    @16
    @1
    @13
    @5
    @16
    @2
    cP
    @2
    cpw
    #
    cin
    #
    cuni
    #
    wss
    #
    @1
    @13
    @16
    @2
    @18
    wcel
    @20
    @16
    cP
    @17
    @2
    @16
    id
    @2
    cP
    pwidg
    elind
    @2
    @18
    elssuni
    syl
    @1
    @2
    @4
    @19
    @12
    @1
    @2
    @2
    @2
    cin
    @4
    @2
    inidm
    @2
    @3
    @2
    ineq2
    syl5eqr
    #
    @1
    @18
    @11
    @1
    @17
    @10
    cP
    @1
    @2
    @4
    @21
    pweqd
    ineq2d
    unieqd
    sseq12d
    syl5ibcom
    @5
    @13
    wi
    @16
    @5
    @13
    c0
    @12
    wss
    @12
    0ss
    @4
    c0
    @12
    sseq1
    mpbiri
    a1i
    jaod
    ralimdv
    ralimia
    adantl
    @0
    @9
    @15
    wb
    @8
    vx
    vy
    cP
    cV
    isbasisg
    adantr
    mpbird
end
