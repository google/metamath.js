include "cmd.mm"
include "wbr.mm"
include "cin.mm"
include "wss.mm"
include "wa.mm"
include "w3a.mm"
include "simp1.mm"
include "cch.mm"
include "wcel.mm"
include "chincli.mm"
include "ssmd1.mm"
include "mp3an12.mm"
include "adantr.mm"
include "3ad2ant3.mm"
include "sslin.mm"
include "sstr.mm"
include "sylan.mm"
include "ancoms.mm"
include "ad2ant2rl.mm"
include "3adant1.mm"
include "simp2r.mm"
include "mdslmd3i.mm"
include "syl22anc.mm"
include "wceq.mm"
include "sseqin2.mm"
include "biimpi.mm"
include "adantl.mm"
include "breqtrd.mm"

theorem mdslmd4i
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


  assert |- ( ( A MH B /\ ( ( A i^i B ) C_ C /\ C C_ A ) /\ ( ( A i^i B ) C_ D /\ D C_ B ) ) -> C MH D )

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
    wss
    #
    cC
    cA
    wss
    #
    wa
    #
    @1
    cD
    wss
    #
    cD
    cB
    wss
    #
    wa
    #
    w3a
    #
    cC
    cB
    cD
    cin
    #
    cD
    cmd
    @8
    @0
    @1
    cD
    cmd
    wbr
    #
    cA
    cD
    cin
    #
    cC
    wss
    #
    @3
    cC
    @9
    cmd
    wbr
    @0
    @4
    @7
    simp1
    @7
    @0
    @10
    @4
    @5
    @10
    @6
    @1
    cch
    wcel
    cD
    cch
    wcel
    @5
    @10
    cA
    cB
    mdslmd.1
    mdslmd.2
    chincli
    mdslmd.4
    @1
    cD
    ssmd1
    mp3an12
    adantr
    3ad2ant3
    @4
    @7
    @12
    @0
    @2
    @6
    @12
    @3
    @5
    @6
    @2
    @12
    @6
    @11
    @1
    wss
    @2
    @12
    cD
    cB
    cA
    sslin
    @11
    @1
    cC
    sstr
    sylan
    ancoms
    ad2ant2rl
    3adant1
    @0
    @2
    @3
    @7
    simp2r
    cA
    cB
    cD
    cC
    mdslmd.1
    mdslmd.2
    mdslmd.4
    mdslmd.3
    mdslmd3i
    syl22anc
    @7
    @0
    @9
    cD
    wceq
    #
    @4
    @6
    @13
    @5
    @6
    @13
    cD
    cB
    sseqin2
    biimpi
    adantl
    3ad2ant3
    breqtrd
end
