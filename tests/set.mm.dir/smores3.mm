include "cres.mm"
include "wsmo.mm"
include "cdm.mm"
include "cin.mm"
include "wcel.mm"
include "word.mm"
include "w3a.mm"
include "dmres.mm"
include "incom.mm"
include "eqtri.mm"
include "eleq2i.mm"
include "smores.mm"
include "sylan2br.mm"
include "3adant3.mm"
include "wss.mm"
include "wceq.mm"
include "wb.mm"
include "inss2.mm"
include "sseli.mm"
include "ordelss.mm"
include "ancoms.mm"
include "sylan.mm"
include "3adant1.mm"
include "resabs1.mm"
include "smoeq.mm"
include "3syl.mm"
include "mpbid.mm"

theorem smores3
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( Smo ( A |` B ) /\ C e. ( dom A i^i B ) /\ Ord B ) -> Smo ( A |` C ) )

  proof
    cA
    cB
    cres
    #
    wsmo
    #
    cC
    cA
    cdm
    #
    cB
    cin
    #
    wcel
    #
    cB
    word
    #
    w3a
    #
    @0
    cC
    cres
    #
    wsmo
    #
    cA
    cC
    cres
    #
    wsmo
    #
    @1
    @4
    @8
    @5
    @4
    @1
    cC
    @0
    cdm
    #
    wcel
    @8
    @11
    @3
    cC
    @11
    cB
    @2
    cin
    @3
    cA
    cB
    dmres
    cB
    @2
    incom
    eqtri
    eleq2i
    @0
    cC
    smores
    sylan2br
    3adant3
    @6
    cC
    cB
    wss
    #
    @7
    @9
    wceq
    @8
    @10
    wb
    @4
    @5
    @12
    @1
    @4
    cC
    cB
    wcel
    #
    @5
    @12
    @3
    cB
    cC
    @2
    cB
    inss2
    sseli
    @5
    @13
    @12
    cB
    cC
    ordelss
    ancoms
    sylan
    3adant1
    cA
    cC
    cB
    resabs1
    @7
    @9
    smoeq
    3syl
    mpbid
end
