include "cv.mm"
include "csuc.mm"
include "wceq.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "com.mm"
include "w-bnj17.mm"
include "w3a.mm"
include "bnj312.mm"
include "bnj252.mm"
include "bitri.mm"
include "simplbi.mm"
include "sylbi.mm"
include "simp2bi.mm"
include "simp3bi.mm"
include "jca.mm"
include "necom.mm"
include "eleq2.mm"
include "biimpa.mm"
include "wo.mm"
include "wi.mm"
include "elsuci.mm"
include "orcom.mm"
include "neor.mm"
include "bitr3i.mm"
include "sylib.mm"
include "imp.mm"
include "stoic3.mm"
include "syl3an3b.mm"
include "3expb.mm"
include "syl2an.mm"

theorem bnj563
  let wet: wff et
  let wrh: wff rh
  let cD: class D
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  assume bnj563.19: |- ( et <-> ( m e. D /\ n = suc m /\ p e. _om /\ m = suc p ) )
  assume bnj563.21: |- ( rh <-> ( i e. _om /\ suc i e. n /\ m =/= suc i ) )


  assert |- ( ( et /\ rh ) -> suc i e. m )

  proof
    wet
    vn
    cv
    #
    vm
    cv
    #
    csuc
    #
    wceq
    #
    vi
    cv
    #
    csuc
    #
    @0
    wcel
    #
    @1
    @5
    wne
    #
    wa
    @5
    @1
    wcel
    #
    wrh
    wet
    @1
    cD
    wcel
    #
    @3
    vp
    cv
    #
    com
    wcel
    #
    @1
    @10
    csuc
    wceq
    #
    w-bnj17
    #
    @3
    bnj563.19
    @13
    @3
    @9
    @11
    @12
    w3a
    #
    @13
    @3
    @9
    @11
    @12
    w-bnj17
    @3
    @14
    wa
    @9
    @3
    @11
    @12
    bnj312
    @3
    @9
    @11
    @12
    bnj252
    bitri
    simplbi
    sylbi
    wrh
    @6
    @7
    wrh
    @4
    com
    wcel
    #
    @6
    @7
    bnj563.21
    simp2bi
    wrh
    @15
    @6
    @7
    bnj563.21
    simp3bi
    jca
    @3
    @6
    @7
    @8
    @7
    @3
    @6
    @5
    @1
    wne
    #
    @8
    @1
    @5
    necom
    @3
    @6
    @5
    @2
    wcel
    #
    @16
    @8
    @3
    @6
    @17
    @0
    @2
    @5
    eleq2
    biimpa
    @17
    @16
    @8
    @17
    @8
    @5
    @1
    wceq
    #
    wo
    #
    @16
    @8
    wi
    #
    @5
    @1
    elsuci
    @19
    @18
    @8
    wo
    @20
    @18
    @8
    orcom
    @8
    @5
    @1
    neor
    bitr3i
    sylib
    imp
    stoic3
    syl3an3b
    3expb
    syl2an
end
