include "csuc.mm"
include "wlim.mm"
include "wcel.mm"
include "word.mm"
include "cuni.mm"
include "wceq.mm"
include "wn.mm"
include "limord.mm"
include "ordsuc.mm"
include "sylibr.mm"
include "limuni.mm"
include "ordunisuc.mm"
include "eqeq2d.mm"
include "ordirr.mm"
include "eleq2.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "sucidg.mm"
include "con3i.mm"
include "syl6.mm"
include "sylbid.mm"
include "sylc.mm"
include "con2i.mm"

theorem nlimsucg
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> -. Lim suc A )

  proof
    cA
    csuc
    #
    wlim
    #
    cA
    cV
    wcel
    #
    @1
    cA
    word
    #
    @0
    @0
    cuni
    #
    wceq
    #
    @2
    wn
    #
    @1
    @0
    word
    @3
    @0
    limord
    cA
    ordsuc
    sylibr
    @0
    limuni
    @3
    @5
    @0
    cA
    wceq
    #
    @6
    @3
    @4
    cA
    @0
    cA
    ordunisuc
    eqeq2d
    @3
    @7
    cA
    @0
    wcel
    #
    wn
    #
    @6
    @3
    @9
    @7
    cA
    cA
    wcel
    #
    wn
    cA
    ordirr
    @7
    @8
    @10
    @0
    cA
    cA
    eleq2
    notbid
    syl5ibrcom
    @2
    @8
    cA
    cV
    sucidg
    con3i
    syl6
    sylbid
    sylc
    con2i
end
