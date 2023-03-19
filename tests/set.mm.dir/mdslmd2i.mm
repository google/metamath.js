include "cmd.mm"
include "wbr.mm"
include "cdmd.mm"
include "wa.mm"
include "cin.mm"
include "wss.mm"
include "chj.mm"
include "co.mm"
include "wb.mm"
include "chjcli.mm"
include "chlej1i.mm"
include "chjjdiri.mm"
include "chjcomi.mm"
include "3sstr3g.mm"
include "adantl.mm"
include "chub2i.mm"
include "ssini.mm"
include "jctil.mm"
include "mdslmd1i.mm"
include "sylan2.mm"
include "w3a.mm"
include "wceq.mm"
include "id.mm"
include "inss1.mm"
include "sstr.mm"
include "mpan2.mm"
include "chub1i.mm"
include "mpan.mm"
include "cch.mm"
include "wcel.mm"
include "3pm3.2i.mm"
include "mdsl3.mm"
include "syl3an.mm"
include "inss2.mm"
include "breq12d.mm"
include "3expb.mm"
include "adantlr.mm"
include "bitr2d.mm"

theorem mdslmd2i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x
  let vy: setvar y
  assume mdslmd.1: |- A e. CH
  assume mdslmd.2: |- B e. CH
  assume mdslmd.3: |- C e. CH
  assume mdslmd.4: |- D e. CH


  assert |- ( ( ( A MH B /\ B MH* A ) /\ ( ( A i^i B ) C_ ( C i^i D ) /\ ( C vH D ) C_ B ) ) -> ( C MH D <-> ( C vH A ) MH ( D vH A ) ) )

  proof
    cA
    cB
    cmd
    wbr
    #
    cB
    cA
    cdmd
    wbr
    #
    wa
    #
    cA
    cB
    cin
    #
    cC
    cD
    cin
    #
    wss
    #
    cC
    cD
    chj
    co
    #
    cB
    wss
    #
    wa
    #
    wa
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
    cmd
    wbr
    #
    @9
    cB
    cin
    #
    @10
    cB
    cin
    #
    cmd
    wbr
    #
    cC
    cD
    cmd
    wbr
    #
    @8
    @2
    cA
    @9
    @10
    cin
    wss
    #
    @9
    @10
    chj
    co
    #
    cA
    cB
    chj
    co
    #
    wss
    #
    wa
    @11
    @14
    wb
    @8
    @19
    @16
    @7
    @19
    @5
    @7
    @6
    cA
    chj
    co
    cB
    cA
    chj
    co
    @17
    @18
    @6
    cB
    cA
    cC
    cD
    mdslmd.3
    mdslmd.4
    chjcli
    mdslmd.2
    mdslmd.1
    chlej1i
    cC
    cD
    cA
    mdslmd.3
    mdslmd.4
    mdslmd.1
    chjjdiri
    cB
    cA
    mdslmd.2
    mdslmd.1
    chjcomi
    3sstr3g
    adantl
    cA
    @9
    @10
    cA
    cC
    mdslmd.1
    mdslmd.3
    chub2i
    cA
    cD
    mdslmd.1
    mdslmd.4
    chub2i
    ssini
    jctil
    cA
    cB
    @9
    @10
    mdslmd.1
    mdslmd.2
    cC
    cA
    mdslmd.3
    mdslmd.1
    chjcli
    cD
    cA
    mdslmd.4
    mdslmd.1
    chjcli
    mdslmd1i
    sylan2
    @0
    @8
    @14
    @15
    wb
    #
    @1
    @0
    @5
    @7
    @20
    @0
    @5
    @7
    w3a
    @12
    cC
    @13
    cD
    cmd
    @0
    @0
    @5
    @3
    cC
    wss
    #
    @7
    cC
    cB
    wss
    #
    @12
    cC
    wceq
    #
    @0
    id
    #
    @5
    @4
    cC
    wss
    @21
    cC
    cD
    inss1
    @3
    @4
    cC
    sstr
    mpan2
    cC
    @6
    wss
    @7
    @22
    cC
    cD
    mdslmd.3
    mdslmd.4
    chub1i
    cC
    @6
    cB
    sstr
    mpan
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
    @21
    @22
    w3a
    @23
    @25
    @26
    @27
    mdslmd.1
    mdslmd.2
    mdslmd.3
    3pm3.2i
    cA
    cB
    cC
    mdsl3
    mpan
    syl3an
    @0
    @0
    @5
    @3
    cD
    wss
    #
    @7
    cD
    cB
    wss
    #
    @13
    cD
    wceq
    #
    @24
    @5
    @4
    cD
    wss
    @28
    cC
    cD
    inss2
    @3
    @4
    cD
    sstr
    mpan2
    cD
    @6
    wss
    @7
    @29
    cD
    cC
    mdslmd.4
    mdslmd.3
    chub2i
    cD
    @6
    cB
    sstr
    mpan
    @25
    @26
    cD
    cch
    wcel
    #
    w3a
    @0
    @28
    @29
    w3a
    @30
    @25
    @26
    @31
    mdslmd.1
    mdslmd.2
    mdslmd.4
    3pm3.2i
    cA
    cB
    cD
    mdsl3
    mpan
    syl3an
    breq12d
    3expb
    adantlr
    bitr2d
end
