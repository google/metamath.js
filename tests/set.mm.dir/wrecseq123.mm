include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "wfn.mm"
include "wss.mm"
include "cpred.mm"
include "wral.mm"
include "wa.mm"
include "cfv.mm"
include "cres.mm"
include "wex.mm"
include "cab.mm"
include "cuni.mm"
include "cwrecs.mm"
include "wb.mm"
include "sseq2.mm"
include "3ad2ant2.mm"
include "predeq1.mm"
include "predeq2.mm"
include "sylan9eq.mm"
include "3adant3.mm"
include "sseq1d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "simp3.mm"
include "reseq2d.mm"
include "fveq12d.mm"
include "eqeq2d.mm"
include "3anbi23d.mm"
include "exbidv.mm"
include "abbidv.mm"
include "unieqd.mm"
include "df-wrecs.mm"
include "3eqtr4g.mm"

theorem wrecseq123
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( R = S /\ A = B /\ F = G ) -> wrecs ( R , A , F ) = wrecs ( S , B , G ) )

  proof
    cR
    cS
    wceq
    #
    cA
    cB
    wceq
    #
    cF
    cG
    wceq
    #
    w3a
    #
    vf
    cv
    #
    vx
    cv
    #
    wfn
    #
    @5
    cA
    wss
    #
    cA
    cR
    vy
    cv
    #
    cpred
    #
    @5
    wss
    #
    vy
    @5
    wral
    #
    wa
    #
    @8
    @4
    cfv
    #
    @4
    @9
    cres
    #
    cF
    cfv
    #
    wceq
    #
    vy
    @5
    wral
    #
    w3a
    #
    vx
    wex
    #
    vf
    cab
    #
    cuni
    @6
    @5
    cB
    wss
    #
    cB
    cS
    @8
    cpred
    #
    @5
    wss
    #
    vy
    @5
    wral
    #
    wa
    #
    @13
    @4
    @22
    cres
    #
    cG
    cfv
    #
    wceq
    #
    vy
    @5
    wral
    #
    w3a
    #
    vx
    wex
    #
    vf
    cab
    #
    cuni
    cA
    cR
    cF
    cwrecs
    cB
    cS
    cG
    cwrecs
    @3
    @20
    @32
    @3
    @19
    @31
    vf
    @3
    @18
    @30
    vx
    @3
    @12
    @25
    @17
    @29
    @6
    @3
    @7
    @21
    @11
    @24
    @1
    @0
    @7
    @21
    wb
    @2
    cA
    cB
    @5
    sseq2
    3ad2ant2
    @3
    @10
    @23
    vy
    @5
    @3
    @9
    @22
    @5
    @0
    @1
    @9
    @22
    wceq
    @2
    @0
    @1
    @9
    cA
    cS
    @8
    cpred
    @22
    cA
    cR
    cS
    @8
    predeq1
    cA
    cB
    cS
    @8
    predeq2
    sylan9eq
    #
    3adant3
    sseq1d
    ralbidv
    anbi12d
    @3
    @16
    @28
    vy
    @5
    @3
    @15
    @27
    @13
    @3
    @14
    @26
    cF
    cG
    @0
    @1
    @2
    simp3
    @0
    @1
    @14
    @26
    wceq
    @2
    @0
    @1
    wa
    @9
    @22
    @4
    @33
    reseq2d
    3adant3
    fveq12d
    eqeq2d
    ralbidv
    3anbi23d
    exbidv
    abbidv
    unieqd
    vx
    vy
    cA
    cR
    vf
    cF
    df-wrecs
    vx
    vy
    cB
    cS
    vf
    cG
    df-wrecs
    3eqtr4g
end
