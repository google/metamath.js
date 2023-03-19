include "wss.mm"
include "wral.mm"
include "cixp.mm"
include "weq.mm"
include "cif.mm"
include "ciin.mm"
include "cin.mm"
include "cv.mm"
include "wfn.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "simprl.mm"
include "wi.mm"
include "ssel.mm"
include "ral2imi.mm"
include "adantr.mm"
include "impr.mm"
include "eleq2.mm"
include "simplr.mm"
include "wn.mm"
include "ssel2.mm"
include "ifbothda.mm"
include "ex.mm"
include "jca.mm"
include "ralrimivw.mm"
include "jca31.mm"
include "simprll.mm"
include "simpr.mm"
include "ralimi.mm"
include "ralcom.mm"
include "wceq.mm"
include "iftrue.mm"
include "equcoms.mm"
include "eleq2d.mm"
include "rspcva.mm"
include "ralimiaa.mm"
include "sylbi.mm"
include "syl.mm"
include "ad2antll.mm"
include "impbida.mm"
include "vex.mm"
include "elixp.mm"
include "elin.mm"
include "cvv.mm"
include "wb.mm"
include "eliin.mm"
include "ax-mp.mm"
include "ralbii.mm"
include "bitri.mm"
include "anbi12i.mm"
include "3bitr4g.mm"
include "eqrdv.mm"

theorem boxriin
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cI: class I
  let vz: setvar z

  disjoint A y
  disjoint B y
  disjoint I x
  disjoint I y
  disjoint x y
  disjoint A z
  disjoint y z
  disjoint B z
  disjoint I z
  disjoint x z
  assert |- ( A. x e. I A C_ B -> X_ x e. I A = ( X_ x e. I B i^i |^|_ y e. I X_ x e. I if ( x = y , A , B ) ) )

  proof
    cA
    cB
    wss
    #
    vx
    cI
    wral
    #
    vz
    vx
    cI
    cA
    cixp
    #
    vx
    cI
    cB
    cixp
    #
    vy
    cI
    vx
    cI
    vx
    vy
    weq
    #
    cA
    cB
    cif
    #
    cixp
    #
    ciin
    #
    cin
    #
    @1
    vz
    cv
    #
    cI
    wfn
    #
    vx
    cv
    #
    @9
    cfv
    #
    cA
    wcel
    #
    vx
    cI
    wral
    #
    wa
    #
    @10
    @12
    cB
    wcel
    #
    vx
    cI
    wral
    #
    wa
    #
    @10
    @12
    @5
    wcel
    #
    vx
    cI
    wral
    #
    wa
    #
    vy
    cI
    wral
    #
    wa
    #
    @9
    @2
    wcel
    @9
    @8
    wcel
    #
    @1
    @15
    @23
    @1
    @15
    wa
    #
    @10
    @17
    @22
    @1
    @10
    @14
    simprl
    #
    @1
    @10
    @14
    @17
    @1
    @14
    @17
    wi
    @10
    @0
    @13
    @16
    vx
    cI
    cA
    cB
    @12
    ssel
    ral2imi
    adantr
    impr
    @25
    @21
    vy
    cI
    @25
    @10
    @20
    @26
    @1
    @10
    @14
    @20
    @1
    @14
    @20
    wi
    @10
    @0
    @13
    @19
    vx
    cI
    @0
    @13
    @19
    @4
    @13
    @16
    @19
    @0
    @13
    wa
    #
    cA
    cB
    cA
    @5
    @12
    eleq2
    cB
    @5
    @12
    eleq2
    @0
    @13
    @4
    simplr
    @27
    @16
    @4
    wn
    cA
    cB
    @12
    ssel2
    adantr
    ifbothda
    ex
    ral2imi
    adantr
    impr
    jca
    ralrimivw
    jca31
    @1
    @23
    wa
    @10
    @14
    @1
    @10
    @17
    @22
    simprll
    @22
    @14
    @1
    @18
    @22
    @20
    vy
    cI
    wral
    #
    @14
    @21
    @20
    vy
    cI
    @10
    @20
    simpr
    ralimi
    @28
    @19
    vy
    cI
    wral
    #
    vx
    cI
    wral
    @14
    @19
    vy
    vx
    cI
    cI
    ralcom
    @29
    @13
    vx
    cI
    @19
    @13
    vy
    @11
    cI
    vy
    vx
    weq
    @5
    cA
    @12
    @5
    cA
    wceq
    vx
    vy
    @4
    cA
    cB
    iftrue
    equcoms
    eleq2d
    rspcva
    ralimiaa
    sylbi
    syl
    ad2antll
    jca
    impbida
    vx
    cI
    cA
    @9
    vz
    vex
    #
    elixp
    @24
    @9
    @3
    wcel
    #
    @9
    @7
    wcel
    #
    wa
    @23
    @9
    @3
    @7
    elin
    @31
    @18
    @32
    @22
    vx
    cI
    cB
    @9
    @30
    elixp
    @32
    @9
    @6
    wcel
    #
    vy
    cI
    wral
    #
    @22
    @9
    cvv
    wcel
    @32
    @34
    wb
    @30
    vy
    @9
    cI
    @6
    cvv
    eliin
    ax-mp
    @33
    @21
    vy
    cI
    vx
    cI
    @5
    @9
    @30
    elixp
    ralbii
    bitri
    anbi12i
    bitri
    3bitr4g
    eqrdv
end
