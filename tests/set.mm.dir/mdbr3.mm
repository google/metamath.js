include "cch.mm"
include "wcel.mm"
include "wa.mm"
include "cmd.mm"
include "wbr.mm"
include "cv.mm"
include "wss.mm"
include "chj.mm"
include "co.mm"
include "cin.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "mdbr.mm"
include "wb.mm"
include "chincl.mm"
include "inss2.mm"
include "sseq1.mm"
include "oveq1.mm"
include "ineq1d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "mpii.mm"
include "syl.mm"
include "ex.mm"
include "com3l.mm"
include "ralrimdv.mm"
include "dfss.mm"
include "biimpi.mm"
include "oveq1d.mm"
include "biimprcd.mm"
include "ralimi.mm"
include "cbvralv.mm"
include "sylib.mm"
include "impbid1.mm"
include "adantl.mm"
include "bitrd.mm"

theorem mdbr3
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
  assert |- ( ( A e. CH /\ B e. CH ) -> ( A MH B <-> A. x e. CH ( ( ( x i^i B ) vH A ) i^i B ) = ( ( x i^i B ) vH ( A i^i B ) ) ) )

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
    cmd
    wbr
    vy
    cv
    #
    cB
    wss
    #
    @2
    cA
    chj
    co
    #
    cB
    cin
    #
    @2
    cA
    cB
    cin
    #
    chj
    co
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
    cin
    #
    cA
    chj
    co
    #
    cB
    cin
    #
    @12
    @6
    chj
    co
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
    mdbr
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
    #
    @18
    @1
    wa
    @12
    cch
    wcel
    #
    @19
    @11
    cB
    chincl
    @20
    @10
    @12
    cB
    wss
    #
    @16
    @11
    cB
    inss2
    @9
    @21
    @16
    wi
    vy
    @12
    cch
    @2
    @12
    wceq
    #
    @3
    @21
    @8
    @16
    @2
    @12
    cB
    sseq1
    @22
    @5
    @14
    @7
    @15
    @22
    @4
    @13
    cB
    @2
    @12
    cA
    chj
    oveq1
    ineq1d
    @2
    @12
    @6
    chj
    oveq1
    eqeq12d
    imbi12d
    rspcv
    mpii
    syl
    ex
    com3l
    ralrimdv
    @17
    @11
    cB
    wss
    #
    @11
    cA
    chj
    co
    #
    cB
    cin
    #
    @11
    @6
    chj
    co
    #
    wceq
    #
    wi
    #
    vx
    cch
    wral
    @10
    @16
    @28
    vx
    cch
    @23
    @27
    @16
    @23
    @25
    @14
    @26
    @15
    @23
    @24
    @13
    cB
    @23
    @11
    @12
    cA
    chj
    @23
    @11
    @12
    wceq
    @11
    cB
    dfss
    biimpi
    #
    oveq1d
    ineq1d
    @23
    @11
    @12
    @6
    chj
    @29
    oveq1d
    eqeq12d
    biimprcd
    ralimi
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
    sseq1
    @30
    @25
    @5
    @26
    @7
    @30
    @24
    @4
    cB
    @11
    @2
    cA
    chj
    oveq1
    ineq1d
    @11
    @2
    @6
    chj
    oveq1
    eqeq12d
    imbi12d
    cbvralv
    sylib
    impbid1
    adantl
    bitrd
end
