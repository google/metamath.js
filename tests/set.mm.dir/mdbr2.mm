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
include "chub1.mm"
include "ancoms.mm"
include "iba.mm"
include "ssin.mm"
include "syl6bb.mm"
include "syl5ibcom.mm"
include "chub2.mm"
include "ssrin.mm"
include "syl.mm"
include "jctird.mm"
include "adantlr.mm"
include "simpr.mm"
include "chincl.mm"
include "adantr.mm"
include "chjcl.mm"
include "sylan.mm"
include "an32s.mm"
include "chlub.mm"
include "syl3anc.mm"
include "sylibd.mm"
include "eqss.mm"
include "rbaib.mm"
include "syl6.mm"
include "pm5.74d.mm"
include "ralbidva.mm"
include "bitrd.mm"

theorem mdbr2
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
  assert |- ( ( A e. CH /\ B e. CH ) -> ( A MH B <-> A. x e. CH ( x C_ B -> ( ( x vH A ) i^i B ) C_ ( x vH ( A i^i B ) ) ) ) )

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
    cmd
    wbr
    vx
    cv
    #
    cB
    wss
    #
    @3
    cA
    chj
    co
    #
    cB
    cin
    #
    @3
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
    vx
    cch
    wral
    @4
    @6
    @8
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
    mdbr
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
    @8
    @6
    wss
    #
    @9
    @11
    wb
    @14
    @4
    @3
    @6
    wss
    #
    @7
    @6
    wss
    #
    wa
    #
    @15
    @0
    @13
    @4
    @18
    wi
    @1
    @0
    @13
    wa
    #
    @4
    @16
    @17
    @19
    @3
    @5
    wss
    #
    @4
    @16
    @13
    @0
    @20
    @3
    cA
    chub1
    ancoms
    @4
    @20
    @20
    @4
    wa
    @16
    @4
    @20
    iba
    @3
    @5
    cB
    ssin
    syl6bb
    syl5ibcom
    @19
    cA
    @5
    wss
    @17
    cA
    @3
    chub2
    cA
    @5
    cB
    ssrin
    syl
    jctird
    adantlr
    @14
    @13
    @7
    cch
    wcel
    #
    @6
    cch
    wcel
    #
    @18
    @15
    wb
    @2
    @13
    simpr
    @2
    @21
    @13
    cA
    cB
    chincl
    adantr
    @0
    @13
    @1
    @22
    @19
    @5
    cch
    wcel
    #
    @1
    @22
    @13
    @0
    @23
    @3
    cA
    chjcl
    ancoms
    @5
    cB
    chincl
    sylan
    an32s
    @3
    @7
    @6
    chlub
    syl3anc
    sylibd
    @9
    @11
    @15
    @6
    @8
    eqss
    rbaib
    syl6
    pm5.74d
    ralbidva
    bitrd
end
