include "c2.mm"
include "co.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cclwwlkn.mm"
include "crab.mm"
include "chash.mm"
include "c1.mm"
include "cpr.mm"
include "wcel.mm"
include "w3a.mm"
include "cword.mm"
include "clwwlknon2.mm"
include "wa.mm"
include "cvtx.mm"
include "cedg.mm"
include "clwwlkn2.mm"
include "anbi1i.mm"
include "3anan12.mm"
include "anass.mm"
include "eqcomi.mm"
include "wrdeqi.mm"
include "eleq2i.mm"
include "df-3an.mm"
include "anbi2i.mm"
include "bitr2i.mm"
include "anbi12i.mm"
include "bitri.mm"
include "rabbia2.mm"
include "eqtri.mm"

theorem clwwlknon2x
  let vw: setvar w
  let cC: class C
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  assume clwwlknon2.c: |- C = ( ClWWalksNOn ` G )
  assume clwwlknon2x.v: |- V = ( Vtx ` G )
  assume clwwlknon2x.e: |- E = ( Edg ` G )

  disjoint G w
  disjoint X w
  assert |- ( X C 2 ) = { w e. Word V | ( ( # ` w ) = 2 /\ { ( w ` 0 ) , ( w ` 1 ) } e. E /\ ( w ` 0 ) = X ) }

  proof
    cX
    c2
    cC
    co
    cc0
    vw
    cv
    #
    cfv
    #
    cX
    wceq
    #
    vw
    c2
    cG
    cclwwlkn
    co
    #
    crab
    @0
    chash
    cfv
    c2
    wceq
    #
    @1
    c1
    @0
    cfv
    cpr
    #
    cE
    wcel
    #
    @2
    w3a
    #
    vw
    cV
    cword
    #
    crab
    vw
    cC
    cG
    cX
    clwwlknon2.c
    clwwlknon2
    @2
    @7
    vw
    @3
    @8
    @0
    @3
    wcel
    #
    @2
    wa
    @4
    @0
    cG
    cvtx
    cfv
    #
    cword
    #
    wcel
    #
    @5
    cG
    cedg
    cfv
    #
    wcel
    #
    w3a
    #
    @2
    wa
    #
    @0
    @8
    wcel
    #
    @7
    wa
    #
    @9
    @15
    @2
    cG
    @0
    clwwlkn2
    anbi1i
    @16
    @12
    @4
    @14
    wa
    #
    wa
    #
    @2
    wa
    #
    @18
    @15
    @20
    @2
    @4
    @12
    @14
    3anan12
    anbi1i
    @21
    @12
    @19
    @2
    wa
    #
    wa
    @18
    @12
    @19
    @2
    anass
    @12
    @17
    @22
    @7
    @11
    @8
    @0
    @10
    cV
    cV
    @10
    clwwlknon2x.v
    eqcomi
    wrdeqi
    eleq2i
    @7
    @4
    @6
    wa
    #
    @2
    wa
    @22
    @4
    @6
    @2
    df-3an
    @23
    @19
    @2
    @6
    @14
    @4
    cE
    @13
    @5
    clwwlknon2x.e
    eleq2i
    anbi2i
    anbi1i
    bitr2i
    anbi12i
    bitri
    bitri
    bitri
    rabbia2
    eqtri
end
