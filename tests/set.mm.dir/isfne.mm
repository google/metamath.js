include "wcel.mm"
include "cfne.mm"
include "wbr.mm"
include "wceq.mm"
include "cv.mm"
include "cpw.mm"
include "cin.mm"
include "cuni.mm"
include "wss.mm"
include "wral.mm"
include "wa.mm"
include "cvv.mm"
include "fnerel.mm"
include "brrelexi.mm"
include "anim1i.mm"
include "ancoms.mm"
include "simpr.mm"
include "3eqtr3g.mm"
include "uniexg.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "uniexb.mm"
include "sylibr.mm"
include "simpl.mm"
include "jca.mm"
include "syldan.mm"
include "adantrr.mm"
include "unieq.mm"
include "syl6eqr.mm"
include "eqeq1d.mm"
include "raleq.mm"
include "anbi12d.mm"
include "eqeq2d.mm"
include "ineq1.mm"
include "unieqd.mm"
include "sseq2d.mm"
include "ralbidv.mm"
include "df-fne.mm"
include "brabg.mm"
include "pm5.21nd.mm"

theorem isfne
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vs: setvar s
  let vy: setvar y
  let vz: setvar z
  assume isfne.1: |- X = U. A
  assume isfne.2: |- Y = U. B

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint r s
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B r
  disjoint B s
  disjoint B y
  disjoint B z
  disjoint C y
  disjoint C z
  disjoint X r
  disjoint X s
  disjoint Y r
  disjoint Y s
  assert |- ( B e. C -> ( A Fne B <-> ( X = Y /\ A. x e. A x C_ U. ( B i^i ~P x ) ) ) )

  proof
    cB
    cC
    wcel
    #
    cA
    cB
    cfne
    wbr
    #
    cX
    cY
    wceq
    #
    vx
    cv
    #
    cB
    @3
    cpw
    #
    cin
    #
    cuni
    #
    wss
    #
    vx
    cA
    wral
    #
    wa
    #
    cA
    cvv
    wcel
    #
    @0
    wa
    #
    @1
    @0
    @11
    @1
    @10
    @0
    cA
    cB
    cfne
    fnerel
    brrelexi
    anim1i
    ancoms
    @0
    @2
    @11
    @8
    @0
    @2
    cA
    cuni
    #
    cB
    cuni
    #
    wceq
    #
    @11
    @0
    @2
    wa
    cX
    cY
    @12
    @13
    @0
    @2
    simpr
    isfne.1
    isfne.2
    3eqtr3g
    @0
    @14
    wa
    #
    @10
    @0
    @15
    @12
    cvv
    wcel
    @10
    @15
    @12
    @13
    cvv
    @0
    @14
    simpr
    @0
    @13
    cvv
    wcel
    @14
    cB
    cC
    uniexg
    adantr
    eqeltrd
    cA
    uniexb
    sylibr
    @0
    @14
    simpl
    jca
    syldan
    adantrr
    vr
    cv
    #
    cuni
    #
    vs
    cv
    #
    cuni
    #
    wceq
    #
    @3
    @18
    @4
    cin
    #
    cuni
    #
    wss
    #
    vx
    @16
    wral
    #
    wa
    cX
    @19
    wceq
    #
    @23
    vx
    cA
    wral
    #
    wa
    @9
    vr
    vs
    cA
    cB
    cvv
    cC
    cfne
    @16
    cA
    wceq
    #
    @20
    @25
    @24
    @26
    @27
    @17
    cX
    @19
    @27
    @17
    @12
    cX
    @16
    cA
    unieq
    isfne.1
    syl6eqr
    eqeq1d
    @23
    vx
    @16
    cA
    raleq
    anbi12d
    @18
    cB
    wceq
    #
    @25
    @2
    @26
    @8
    @28
    @19
    cY
    cX
    @28
    @19
    @13
    cY
    @18
    cB
    unieq
    isfne.2
    syl6eqr
    eqeq2d
    @28
    @23
    @7
    vx
    cA
    @28
    @22
    @6
    @3
    @28
    @21
    @5
    @18
    cB
    @4
    ineq1
    unieqd
    sseq2d
    ralbidv
    anbi12d
    vr
    vs
    vx
    df-fne
    brabg
    pm5.21nd
end
