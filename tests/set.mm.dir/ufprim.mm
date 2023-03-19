include "cufil.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "wo.mm"
include "cun.mm"
include "wa.mm"
include "cfil.mm"
include "ufilfil.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "simpr.mm"
include "unss.mm"
include "biimpi.mm"
include "3adant1.mm"
include "ssun1.mm"
include "a1i.mm"
include "filss.mm"
include "syl13anc.mm"
include "ex.mm"
include "ssun2.mm"
include "jaod.mm"
include "wn.mm"
include "cdif.mm"
include "wb.mm"
include "ufilb.mm"
include "3adant3.mm"
include "cin.mm"
include "difun2.mm"
include "uncom.mm"
include "difeq1i.mm"
include "eqtr3i.mm"
include "ineq2i.mm"
include "indifcom.mm"
include "3eqtr4i.mm"
include "filin.mm"
include "syl3an1.mm"
include "syl5eqel.mm"
include "simp13.mm"
include "inss1.mm"
include "3expia.mm"
include "sylbid.mm"
include "orrd.mm"
include "impbid.mm"

theorem ufprim
  let cA: class A
  let cB: class B
  let cF: class F
  let cX: class X
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cG: class G


  assert |- ( ( F e. ( UFil ` X ) /\ A C_ X /\ B C_ X ) -> ( ( A e. F \/ B e. F ) <-> ( A u. B ) e. F ) )

  proof
    cF
    cX
    cufil
    cfv
    wcel
    #
    cA
    cX
    wss
    #
    cB
    cX
    wss
    #
    w3a
    #
    cA
    cF
    wcel
    #
    cB
    cF
    wcel
    #
    wo
    #
    cA
    cB
    cun
    #
    cF
    wcel
    #
    @3
    @4
    @8
    @5
    @3
    @4
    @8
    @3
    @4
    wa
    #
    cF
    cX
    cfil
    cfv
    wcel
    #
    @4
    @7
    cX
    wss
    #
    cA
    @7
    wss
    #
    @8
    @3
    @10
    @4
    @0
    @1
    @10
    @2
    cF
    cX
    ufilfil
    3ad2ant1
    #
    adantr
    @3
    @4
    simpr
    @3
    @11
    @4
    @1
    @2
    @11
    @0
    @1
    @2
    wa
    @11
    cA
    cB
    cX
    unss
    biimpi
    3adant1
    #
    adantr
    @12
    @9
    cA
    cB
    ssun1
    a1i
    cA
    @7
    cF
    cX
    filss
    syl13anc
    ex
    @3
    @5
    @8
    @3
    @5
    wa
    #
    @10
    @5
    @11
    cB
    @7
    wss
    #
    @8
    @3
    @10
    @5
    @13
    adantr
    @3
    @5
    simpr
    @3
    @11
    @5
    @14
    adantr
    @16
    @15
    cB
    cA
    ssun2
    a1i
    cB
    @7
    cF
    cX
    filss
    syl13anc
    ex
    jaod
    @3
    @8
    @6
    @3
    @8
    wa
    #
    @4
    @5
    @17
    @4
    wn
    #
    cX
    cA
    cdif
    #
    cF
    wcel
    #
    @5
    @3
    @18
    @20
    wb
    #
    @8
    @0
    @1
    @21
    @2
    cA
    cF
    cX
    ufilb
    3adant3
    adantr
    @3
    @8
    @20
    @5
    @3
    @8
    @20
    w3a
    #
    @10
    cB
    @19
    cin
    #
    cF
    wcel
    @2
    @23
    cB
    wss
    #
    @5
    @3
    @8
    @10
    @20
    @13
    3ad2ant1
    @22
    @23
    @7
    @19
    cin
    #
    cF
    cX
    cB
    cA
    cdif
    #
    cin
    cX
    @7
    cA
    cdif
    #
    cin
    @23
    @25
    @26
    @27
    cX
    cB
    cA
    cun
    #
    cA
    cdif
    @26
    @27
    cB
    cA
    difun2
    @28
    @7
    cA
    cB
    cA
    uncom
    difeq1i
    eqtr3i
    ineq2i
    cB
    cX
    cA
    indifcom
    @7
    cX
    cA
    indifcom
    3eqtr4i
    @3
    @10
    @8
    @20
    @25
    cF
    wcel
    @13
    @7
    @19
    cF
    cX
    filin
    syl3an1
    syl5eqel
    @0
    @1
    @2
    @8
    @20
    simp13
    @24
    @22
    cB
    @19
    inss1
    a1i
    @23
    cB
    cF
    cX
    filss
    syl13anc
    3expia
    sylbid
    orrd
    ex
    impbid
end
