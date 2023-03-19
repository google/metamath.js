include "cmd.mm"
include "wbr.mm"
include "cin.mm"
include "wss.mm"
include "chj.mm"
include "co.mm"
include "w3a.mm"
include "chlej1i.mm"
include "ssrin.mm"
include "wceq.mm"
include "id.mm"
include "wa.mm"
include "ssin.mm"
include "bicomi.mm"
include "simplbi.mm"
include "chlubi.mm"
include "cch.mm"
include "wcel.mm"
include "3pm3.2i.mm"
include "mdsl3.mm"
include "mpan.mm"
include "syl3an.mm"
include "simprbi.mm"
include "sseq12d.mm"
include "syl5ib.mm"
include "impbid2.mm"

theorem mdslle2i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume mdslle1.1: |- A e. CH
  assume mdslle1.2: |- B e. CH
  assume mdslle1.3: |- C e. CH
  assume mdslle1.4: |- D e. CH


  assert |- ( ( A MH B /\ ( A i^i B ) C_ ( C i^i D ) /\ ( C vH D ) C_ B ) -> ( C C_ D <-> ( C vH A ) C_ ( D vH A ) ) )

  proof
    cA
    cB
    cmd
    wbr
    #
    cA
    cB
    cin
    #
    cC
    cD
    cin
    wss
    #
    cC
    cD
    chj
    co
    cB
    wss
    #
    w3a
    #
    cC
    cD
    wss
    #
    cC
    cA
    chj
    co
    #
    cD
    cA
    chj
    co
    #
    wss
    #
    cC
    cD
    cA
    mdslle1.3
    mdslle1.4
    mdslle1.1
    chlej1i
    @8
    @6
    cB
    cin
    #
    @7
    cB
    cin
    #
    wss
    @4
    @5
    @6
    @7
    cB
    ssrin
    @4
    @9
    cC
    @10
    cD
    @0
    @0
    @2
    @1
    cC
    wss
    #
    @3
    cC
    cB
    wss
    #
    @9
    cC
    wceq
    #
    @0
    id
    #
    @2
    @11
    @1
    cD
    wss
    #
    @11
    @15
    wa
    @2
    @1
    cC
    cD
    ssin
    bicomi
    #
    simplbi
    @3
    @12
    cD
    cB
    wss
    #
    @12
    @17
    wa
    @3
    cC
    cD
    cB
    mdslle1.3
    mdslle1.4
    mdslle1.2
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
    mdsl3
    mpan
    syl3an
    @0
    @0
    @2
    @15
    @3
    @17
    @10
    cD
    wceq
    #
    @14
    @2
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
    mdsl3
    mpan
    syl3an
    sseq12d
    syl5ib
    impbid2
end
