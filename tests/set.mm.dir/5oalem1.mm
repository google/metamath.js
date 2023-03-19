include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "cmv.mm"
include "cph.mm"
include "cin.mm"
include "simplll.mm"
include "chil.mm"
include "sheli.mm"
include "ad2antrr.mm"
include "adantr.mm"
include "hvaddsub12.mm"
include "3anidm23.mm"
include "c0v.mm"
include "hvsubid.mm"
include "oveq2d.mm"
include "ax-hvaddid.mm"
include "sylan9eqr.mm"
include "eqtr3d.mm"
include "syl2an.mm"
include "shsvai.mm"
include "adantl.mm"
include "eqeltrrd.mm"
include "elind.mm"
include "simpllr.mm"
include "shscli.mm"
include "shincli.mm"
include "shscomi.mm"
include "syl6eleq.mm"
include "syl2anc.mm"
include "wb.mm"
include "eleq1.mm"
include "ad2antlr.mm"
include "mpbird.mm"

theorem 5oalem1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume 5oalem1.1: |- A e. SH
  assume 5oalem1.2: |- B e. SH
  assume 5oalem1.3: |- C e. SH
  assume 5oalem1.4: |- R e. SH


  assert |- ( ( ( ( x e. A /\ y e. B ) /\ v = ( x +h y ) ) /\ ( z e. C /\ ( x -h z ) e. R ) ) -> v e. ( B +H ( A i^i ( C +H R ) ) ) )

  proof
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    #
    vv
    cv
    #
    @0
    @2
    cva
    co
    #
    wceq
    #
    wa
    #
    vz
    cv
    #
    cC
    wcel
    #
    @0
    @9
    cmv
    co
    #
    cR
    wcel
    #
    wa
    #
    wa
    #
    @5
    cB
    cA
    cC
    cR
    cph
    co
    #
    cin
    #
    cph
    co
    #
    wcel
    #
    @6
    @17
    wcel
    #
    @14
    @0
    @16
    wcel
    #
    @3
    @19
    @14
    cA
    @15
    @0
    @1
    @3
    @7
    @13
    simplll
    @14
    @9
    @11
    cva
    co
    #
    @0
    @15
    @8
    @0
    chil
    wcel
    #
    @9
    chil
    wcel
    #
    @21
    @0
    wceq
    @13
    @1
    @22
    @3
    @7
    @0
    cA
    5oalem1.1
    sheli
    ad2antrr
    @10
    @23
    @12
    @9
    cC
    5oalem1.3
    sheli
    adantr
    @22
    @23
    wa
    @0
    @9
    @9
    cmv
    co
    #
    cva
    co
    #
    @21
    @0
    @22
    @23
    @25
    @21
    wceq
    @0
    @9
    @9
    hvaddsub12
    3anidm23
    @23
    @22
    @25
    @0
    c0v
    cva
    co
    @0
    @23
    @24
    c0v
    @0
    cva
    @9
    hvsubid
    oveq2d
    @0
    ax-hvaddid
    sylan9eqr
    eqtr3d
    syl2an
    @13
    @21
    @15
    wcel
    @8
    cC
    cR
    @9
    @11
    5oalem1.3
    5oalem1.4
    shsvai
    adantl
    eqeltrrd
    elind
    @1
    @3
    @7
    @13
    simpllr
    @20
    @3
    wa
    @6
    @16
    cB
    cph
    co
    @17
    @16
    cB
    @0
    @2
    cA
    @15
    5oalem1.1
    cC
    cR
    5oalem1.3
    5oalem1.4
    shscli
    shincli
    #
    5oalem1.2
    shsvai
    @16
    cB
    @26
    5oalem1.2
    shscomi
    syl6eleq
    syl2anc
    @7
    @18
    @19
    wb
    @4
    @13
    @5
    @6
    @17
    eleq1
    ad2antlr
    mpbird
end
