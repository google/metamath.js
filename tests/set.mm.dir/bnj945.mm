include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "wfn.mm"
include "csuc.mm"
include "wceq.mm"
include "w-bnj17.mm"
include "wfun.mm"
include "wss.mm"
include "cdm.mm"
include "w3a.mm"
include "cfv.mm"
include "wa.mm"
include "fndm.mm"
include "ad2antll.mm"
include "eleq2d.mm"
include "pm5.32i.mm"
include "bnj941.mm"
include "imp.mm"
include "bnj930.mm"
include "cop.mm"
include "csn.mm"
include "bnj931.mm"
include "jctir.mm"
include "anim1i.mm"
include "sylbir.mm"
include "df-bnj17.mm"
include "3ancomb.mm"
include "3anass.mm"
include "bitri.mm"
include "anbi1i.mm"
include "df-3an.mm"
include "3imtr4i.mm"
include "funssfv.mm"
include "syl.mm"

theorem bnj945
  let cA: class A
  let cC: class C
  let vf: setvar f
  let vn: setvar n
  let cG: class G
  let vp: setvar p
  assume bnj945.1: |- G = ( f u. { <. n , C >. } )


  assert |- ( ( C e. _V /\ f Fn n /\ p = suc n /\ A e. n ) -> ( G ` A ) = ( f ` A ) )

  proof
    cC
    cvv
    wcel
    #
    vf
    cv
    #
    vn
    cv
    #
    wfn
    #
    vp
    cv
    #
    @2
    csuc
    wceq
    #
    cA
    @2
    wcel
    #
    w-bnj17
    #
    cG
    wfun
    #
    @1
    cG
    wss
    #
    cA
    @1
    cdm
    #
    wcel
    #
    w3a
    #
    cA
    cG
    cfv
    cA
    @1
    cfv
    wceq
    @0
    @5
    @3
    wa
    #
    wa
    #
    @6
    wa
    #
    @8
    @9
    wa
    #
    @11
    wa
    #
    @7
    @12
    @15
    @14
    @11
    wa
    @17
    @14
    @11
    @6
    @14
    @10
    @2
    cA
    @3
    @10
    @2
    wceq
    @0
    @5
    @2
    @1
    fndm
    ad2antll
    eleq2d
    pm5.32i
    @14
    @16
    @11
    @14
    @8
    @9
    @14
    @4
    cG
    @0
    @13
    cG
    @4
    wfn
    cC
    vf
    vn
    cG
    vp
    bnj945.1
    bnj941
    imp
    bnj930
    cG
    @1
    @2
    cC
    cop
    csn
    bnj945.1
    bnj931
    jctir
    anim1i
    sylbir
    @7
    @0
    @3
    @5
    w3a
    #
    @6
    wa
    @15
    @0
    @3
    @5
    @6
    df-bnj17
    @18
    @14
    @6
    @18
    @0
    @5
    @3
    w3a
    @14
    @0
    @3
    @5
    3ancomb
    @0
    @5
    @3
    3anass
    bitri
    anbi1i
    bitri
    @8
    @9
    @11
    df-3an
    3imtr4i
    cA
    cG
    @1
    funssfv
    syl
end
