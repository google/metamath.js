include "cdmd.mm"
include "wbr.mm"
include "cin.mm"
include "wss.mm"
include "chj.mm"
include "co.mm"
include "w3a.mm"
include "ssrin.mm"
include "chincli.mm"
include "chlej1i.mm"
include "wceq.mm"
include "id.mm"
include "wa.mm"
include "ssin.mm"
include "bicomi.mm"
include "simplbi.mm"
include "chjcli.mm"
include "chlubi.mm"
include "cch.mm"
include "wcel.mm"
include "3pm3.2i.mm"
include "dmdsl3.mm"
include "mpan.mm"
include "syl3an.mm"
include "simprbi.mm"
include "sseq12d.mm"
include "syl5ib.mm"
include "impbid2.mm"

theorem mdslle1i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume mdslle1.1: |- A e. CH
  assume mdslle1.2: |- B e. CH
  assume mdslle1.3: |- C e. CH
  assume mdslle1.4: |- D e. CH


  assert |- ( ( B MH* A /\ A C_ ( C i^i D ) /\ ( C vH D ) C_ ( A vH B ) ) -> ( C C_ D <-> ( C i^i B ) C_ ( D i^i B ) ) )

  proof
    cB
    cA
    cdmd
    wbr
    #
    cA
    cC
    cD
    cin
    wss
    #
    cC
    cD
    chj
    co
    cA
    cB
    chj
    co
    #
    wss
    #
    w3a
    #
    cC
    cD
    wss
    #
    cC
    cB
    cin
    #
    cD
    cB
    cin
    #
    wss
    #
    cC
    cD
    cB
    ssrin
    @8
    @6
    cA
    chj
    co
    #
    @7
    cA
    chj
    co
    #
    wss
    @4
    @5
    @6
    @7
    cA
    cC
    cB
    mdslle1.3
    mdslle1.2
    chincli
    cD
    cB
    mdslle1.4
    mdslle1.2
    chincli
    mdslle1.1
    chlej1i
    @4
    @9
    cC
    @10
    cD
    @0
    @0
    @1
    cA
    cC
    wss
    #
    @3
    cC
    @2
    wss
    #
    @9
    cC
    wceq
    #
    @0
    id
    #
    @1
    @11
    cA
    cD
    wss
    #
    @11
    @15
    wa
    @1
    cA
    cC
    cD
    ssin
    bicomi
    #
    simplbi
    @3
    @12
    cD
    @2
    wss
    #
    @12
    @17
    wa
    @3
    cC
    cD
    @2
    mdslle1.3
    mdslle1.4
    cA
    cB
    mdslle1.1
    mdslle1.2
    chjcli
    chlubi
    bicomi
    #
    simplbi
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    cC
    cch
    wcel
    #
    w3a
    @0
    @11
    @12
    w3a
    @13
    @19
    @20
    @21
    mdslle1.1
    mdslle1.2
    mdslle1.3
    3pm3.2i
    cA
    cB
    cC
    dmdsl3
    mpan
    syl3an
    @0
    @0
    @1
    @15
    @3
    @17
    @10
    cD
    wceq
    #
    @14
    @1
    @11
    @15
    @16
    simprbi
    @3
    @12
    @17
    @18
    simprbi
    @19
    @20
    cD
    cch
    wcel
    #
    w3a
    @0
    @15
    @17
    w3a
    @22
    @19
    @20
    @23
    mdslle1.1
    mdslle1.2
    mdslle1.4
    3pm3.2i
    cA
    cB
    cD
    dmdsl3
    mpan
    syl3an
    sseq12d
    syl5ib
    impbid2
end
