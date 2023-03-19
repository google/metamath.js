include "cch.mm"
include "wcel.mm"
include "wa.mm"
include "cdmd.mm"
include "wbr.mm"
include "cv.mm"
include "wss.mm"
include "cin.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "dmdbr.mm"
include "wb.mm"
include "chub2.mm"
include "ancoms.mm"
include "chjcl.mm"
include "sseq2.mm"
include "ineq1.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl.mm"
include "mpid.mm"
include "ex.mm"
include "com3l.mm"
include "ralrimdv.mm"
include "chlejb2.mm"
include "biimpa.mm"
include "ineq1d.mm"
include "biimpd.mm"
include "com23.mm"
include "ralimdva.mm"
include "cbvralv.mm"
include "syl6ib.mm"
include "impbid.mm"
include "adantl.mm"
include "bitrd.mm"

theorem dmdbr3
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z
  let cC: class C

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint C x
  assert |- ( ( A e. CH /\ B e. CH ) -> ( A MH* B <-> A. x e. CH ( ( ( x vH B ) i^i A ) vH B ) = ( ( x vH B ) i^i ( A vH B ) ) ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    wa
    cA
    cB
    cdmd
    wbr
    cB
    vy
    cv
    #
    wss
    #
    @2
    cA
    cin
    #
    cB
    chj
    co
    #
    @2
    cA
    cB
    chj
    co
    #
    cin
    #
    wceq
    #
    wi
    #
    vy
    cch
    wral
    #
    vx
    cv
    #
    cB
    chj
    co
    #
    cA
    cin
    #
    cB
    chj
    co
    #
    @12
    @6
    cin
    #
    wceq
    #
    vx
    cch
    wral
    #
    vy
    cA
    cB
    dmdbr
    @1
    @10
    @17
    wb
    @0
    @1
    @10
    @17
    @1
    @10
    @16
    vx
    cch
    @11
    cch
    wcel
    #
    @1
    @10
    @16
    @18
    @1
    @10
    @16
    wi
    @18
    @1
    wa
    #
    @10
    cB
    @12
    wss
    #
    @16
    @1
    @18
    @20
    cB
    @11
    chub2
    ancoms
    @19
    @12
    cch
    wcel
    @10
    @20
    @16
    wi
    #
    wi
    @11
    cB
    chjcl
    @9
    @21
    vy
    @12
    cch
    @2
    @12
    wceq
    #
    @3
    @20
    @8
    @16
    @2
    @12
    cB
    sseq2
    @22
    @5
    @14
    @7
    @15
    @22
    @4
    @13
    cB
    chj
    @2
    @12
    cA
    ineq1
    oveq1d
    @2
    @12
    @6
    ineq1
    eqeq12d
    imbi12d
    rspcv
    syl
    mpid
    ex
    com3l
    ralrimdv
    @1
    @17
    cB
    @11
    wss
    #
    @11
    cA
    cin
    #
    cB
    chj
    co
    #
    @11
    @6
    cin
    #
    wceq
    #
    wi
    #
    vx
    cch
    wral
    @10
    @1
    @16
    @28
    vx
    cch
    @1
    @18
    wa
    #
    @23
    @16
    @27
    @29
    @23
    @16
    @27
    wi
    @29
    @23
    wa
    #
    @16
    @27
    @30
    @14
    @25
    @15
    @26
    @30
    @13
    @24
    cB
    chj
    @30
    @12
    @11
    cA
    @29
    @23
    @12
    @11
    wceq
    cB
    @11
    chlejb2
    biimpa
    #
    ineq1d
    oveq1d
    @30
    @12
    @11
    @6
    @31
    ineq1d
    eqeq12d
    biimpd
    ex
    com23
    ralimdva
    @28
    @9
    vx
    vy
    cch
    @11
    @2
    wceq
    #
    @23
    @3
    @27
    @8
    @11
    @2
    cB
    sseq2
    @32
    @25
    @5
    @26
    @7
    @32
    @24
    @4
    cB
    chj
    @11
    @2
    cA
    ineq1
    oveq1d
    @11
    @2
    @6
    ineq1
    eqeq12d
    imbi12d
    cbvralv
    syl6ib
    impbid
    adantl
    bitrd
end
