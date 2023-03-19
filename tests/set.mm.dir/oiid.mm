include "word.mm"
include "cep.mm"
include "wwe.mm"
include "wse.mm"
include "coi.mm"
include "wiso.mm"
include "cid.mm"
include "cres.mm"
include "wceq.mm"
include "ordwe.mm"
include "epse.mm"
include "a1i.mm"
include "cdm.mm"
include "crn.mm"
include "eqid.mm"
include "oiiso2.mm"
include "sylancl.mm"
include "wb.mm"
include "wsmo.mm"
include "con0.mm"
include "wss.mm"
include "wa.mm"
include "ordsson.mm"
include "oismo.mm"
include "syl.mm"
include "simprd.mm"
include "isoeq5.mm"
include "mpbid.mm"
include "oicl.mm"
include "id.mm"
include "ordiso2.mm"
include "syl3anc.mm"
include "isoeq4.mm"
include "weniso.mm"

theorem oiid
  let cA: class A


  assert |- ( Ord A -> OrdIso ( _E , A ) = ( _I |` A ) )

  proof
    cA
    word
    #
    cA
    cep
    wwe
    #
    cA
    cep
    wse
    #
    cA
    cA
    cep
    cep
    cA
    cep
    coi
    #
    wiso
    #
    @3
    cid
    cA
    cres
    wceq
    cA
    ordwe
    #
    @2
    @0
    cA
    epse
    #
    a1i
    @0
    @3
    cdm
    #
    cA
    cep
    cep
    @3
    wiso
    #
    @4
    @0
    @7
    @3
    crn
    #
    cep
    cep
    @3
    wiso
    #
    @8
    @0
    @1
    @2
    @10
    @5
    @6
    cA
    cep
    @3
    @3
    eqid
    #
    oiiso2
    sylancl
    @0
    @9
    cA
    wceq
    #
    @10
    @8
    wb
    @0
    @3
    wsmo
    #
    @12
    @0
    cA
    con0
    wss
    @13
    @12
    wa
    cA
    ordsson
    cA
    @3
    @11
    oismo
    syl
    simprd
    @7
    @9
    cA
    cep
    cep
    @3
    isoeq5
    syl
    mpbid
    #
    @0
    @7
    cA
    wceq
    #
    @8
    @4
    wb
    @0
    @8
    @7
    word
    #
    @0
    @15
    @14
    @16
    @0
    cA
    cep
    @3
    @11
    oicl
    a1i
    @0
    id
    @7
    cA
    @3
    ordiso2
    syl3anc
    @7
    cA
    cA
    cep
    cep
    @3
    isoeq4
    syl
    mpbid
    cA
    cep
    @3
    weniso
    syl3anc
end
