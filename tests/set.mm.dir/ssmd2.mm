include "cch.mm"
include "wcel.mm"
include "wss.mm"
include "cmd.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "chj.mm"
include "co.mm"
include "cin.mm"
include "wi.mm"
include "wral.mm"
include "inss2.mm"
include "chub2.mm"
include "syl5ss.mm"
include "adantrl.mm"
include "wceq.mm"
include "simpl.mm"
include "sseqin2.mm"
include "sylib.mm"
include "adantl.mm"
include "oveq2d.mm"
include "sseqtr4d.mm"
include "a1d.mm"
include "exp32.mm"
include "ralrimdv.mm"
include "adantr.mm"
include "wb.mm"
include "mdbr2.mm"
include "ancoms.mm"
include "sylibrd.mm"
include "3impia.mm"

theorem ssmd2
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A e. CH /\ B e. CH /\ A C_ B ) -> B MH A )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    cA
    cB
    wss
    #
    cB
    cA
    cmd
    wbr
    #
    @0
    @1
    wa
    @2
    vx
    cv
    #
    cA
    wss
    #
    @4
    cB
    chj
    co
    #
    cA
    cin
    #
    @4
    cB
    cA
    cin
    #
    chj
    co
    #
    wss
    #
    wi
    #
    vx
    cch
    wral
    #
    @3
    @0
    @2
    @12
    wi
    @1
    @0
    @2
    @11
    vx
    cch
    @0
    @2
    @4
    cch
    wcel
    #
    @11
    @0
    @2
    @13
    wa
    #
    wa
    #
    @10
    @5
    @15
    @7
    @4
    cA
    chj
    co
    #
    @9
    @0
    @13
    @7
    @16
    wss
    @2
    @0
    @13
    wa
    @7
    cA
    @16
    @6
    cA
    inss2
    cA
    @4
    chub2
    syl5ss
    adantrl
    @15
    @8
    cA
    @4
    chj
    @14
    @8
    cA
    wceq
    #
    @0
    @14
    @2
    @17
    @2
    @13
    simpl
    cA
    cB
    sseqin2
    sylib
    adantl
    oveq2d
    sseqtr4d
    a1d
    exp32
    ralrimdv
    adantr
    @1
    @0
    @3
    @12
    wb
    vx
    cB
    cA
    mdbr2
    ancoms
    sylibrd
    3impia
end
