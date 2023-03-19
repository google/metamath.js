include "wcel.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "cpw.mm"
include "crab.mm"
include "wa.mm"
include "wb.mm"
include "sseq2.mm"
include "elrab.mm"
include "selpw.mm"
include "anbi1i.mm"
include "bitri.mm"
include "a1i.mm"
include "cvv.mm"
include "elex.mm"
include "3ad2ant1.mm"
include "wsbc.mm"
include "simp2.mm"
include "sbcieg.mm"
include "syl.mm"
include "mpbird.mm"
include "wn.mm"
include "ss0.mm"
include "necon3ai.mm"
include "3ad2ant3.mm"
include "0ex.mm"
include "sbcie.mm"
include "sylnibr.mm"
include "wi.mm"
include "sstr.mm"
include "expcom.mm"
include "vex.mm"
include "3imtr4g.mm"
include "cin.mm"
include "ssin.mm"
include "biimpi.mm"
include "syl2anb.mm"
include "inex1.mm"
include "sylibr.mm"
include "isfild.mm"

theorem supfil
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint B x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint V w
  disjoint V y
  disjoint V z
  assert |- ( ( A e. V /\ B C_ A /\ B =/= (/) ) -> { x e. ~P A | B C_ x } e. ( Fil ` A ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cA
    wss
    #
    cB
    c0
    wne
    #
    w3a
    #
    cB
    vy
    cv
    #
    wss
    #
    vy
    vz
    vw
    cA
    cB
    vx
    cv
    #
    wss
    #
    vx
    cA
    cpw
    #
    crab
    #
    @4
    @9
    wcel
    #
    @4
    cA
    wss
    #
    @5
    wa
    #
    wb
    @3
    @10
    @4
    @8
    wcel
    #
    @5
    wa
    @12
    @7
    @5
    vx
    @4
    @8
    @6
    @4
    cB
    sseq2
    elrab
    @13
    @11
    @5
    vy
    cA
    selpw
    anbi1i
    bitri
    a1i
    @0
    @1
    cA
    cvv
    wcel
    #
    @2
    cA
    cV
    elex
    3ad2ant1
    #
    @3
    @5
    vy
    cA
    wsbc
    #
    @1
    @0
    @1
    @2
    simp2
    @3
    @14
    @16
    @1
    wb
    @15
    @5
    @1
    vy
    cA
    cvv
    @4
    cA
    cB
    sseq2
    sbcieg
    syl
    mpbird
    @3
    cB
    c0
    wss
    #
    @5
    vy
    c0
    wsbc
    @2
    @0
    @17
    wn
    @1
    @17
    cB
    c0
    cB
    ss0
    necon3ai
    3ad2ant3
    @5
    @17
    vy
    c0
    0ex
    @4
    c0
    cB
    sseq2
    sbcie
    sylnibr
    vw
    cv
    #
    vz
    cv
    #
    wss
    #
    @3
    @5
    vy
    @18
    wsbc
    #
    @5
    vy
    @19
    wsbc
    #
    wi
    @19
    cA
    wss
    #
    @20
    cB
    @18
    wss
    #
    cB
    @19
    wss
    #
    @21
    @22
    @24
    @20
    @25
    cB
    @18
    @19
    sstr
    expcom
    @5
    @24
    vy
    @18
    vw
    vex
    @4
    @18
    cB
    sseq2
    sbcie
    #
    @5
    @25
    vy
    @19
    vz
    vex
    #
    @4
    @19
    cB
    sseq2
    sbcie
    #
    3imtr4g
    3ad2ant3
    @22
    @21
    wa
    #
    @5
    vy
    @19
    @18
    cin
    #
    wsbc
    #
    wi
    @3
    @23
    @18
    cA
    wss
    w3a
    @29
    cB
    @30
    wss
    #
    @31
    @22
    @25
    @24
    @32
    @21
    @28
    @26
    @25
    @24
    wa
    @32
    cB
    @19
    @18
    ssin
    biimpi
    syl2anb
    @5
    @32
    vy
    @30
    @19
    @18
    @27
    inex1
    @4
    @30
    cB
    sseq2
    sbcie
    sylibr
    a1i
    isfild
end
