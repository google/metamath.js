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
include "chincl.mm"
include "ancoms.mm"
include "adantlr.mm"
include "simplr.mm"
include "simpr.mm"
include "w3a.mm"
include "inss1.mm"
include "chlub.mm"
include "biimpd.mm"
include "mpani.mm"
include "syl3anc.mm"
include "simpll.mm"
include "inss2.mm"
include "chlej1.mm"
include "mpan2.mm"
include "jctird.mm"
include "ssin.mm"
include "syl6ib.mm"
include "eqss.mm"
include "baib.mm"
include "syl6.mm"
include "pm5.74d.mm"
include "ralbidva.mm"
include "bitrd.mm"

theorem dmdbr2
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
  assert |- ( ( A e. CH /\ B e. CH ) -> ( A MH* B <-> A. x e. CH ( B C_ x -> ( x i^i ( A vH B ) ) C_ ( ( x i^i A ) vH B ) ) ) )

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
    #
    cA
    cB
    cdmd
    wbr
    cB
    vx
    cv
    #
    wss
    #
    @3
    cA
    cin
    #
    cB
    chj
    co
    #
    @3
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
    vx
    cch
    wral
    @4
    @8
    @6
    wss
    #
    wi
    #
    vx
    cch
    wral
    vx
    cA
    cB
    dmdbr
    @2
    @10
    @12
    vx
    cch
    @2
    @3
    cch
    wcel
    #
    wa
    #
    @4
    @9
    @11
    @14
    @4
    @6
    @8
    wss
    #
    @9
    @11
    wb
    @14
    @4
    @6
    @3
    wss
    #
    @6
    @7
    wss
    #
    wa
    @15
    @14
    @4
    @16
    @17
    @14
    @5
    cch
    wcel
    #
    @1
    @13
    @4
    @16
    wi
    @0
    @13
    @18
    @1
    @13
    @0
    @18
    @3
    cA
    chincl
    ancoms
    adantlr
    #
    @0
    @1
    @13
    simplr
    #
    @2
    @13
    simpr
    @18
    @1
    @13
    w3a
    #
    @5
    @3
    wss
    #
    @4
    @16
    @3
    cA
    inss1
    @21
    @22
    @4
    wa
    @16
    @5
    cB
    @3
    chlub
    biimpd
    mpani
    syl3anc
    @14
    @18
    @0
    @1
    @17
    @19
    @0
    @1
    @13
    simpll
    @20
    @18
    @0
    @1
    w3a
    @5
    cA
    wss
    @17
    @3
    cA
    inss2
    @5
    cA
    cB
    chlej1
    mpan2
    syl3anc
    jctird
    @6
    @3
    @7
    ssin
    syl6ib
    @9
    @15
    @11
    @6
    @8
    eqss
    baib
    syl6
    pm5.74d
    ralbidva
    bitrd
end
