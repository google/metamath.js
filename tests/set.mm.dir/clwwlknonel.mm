include "cc0.mm"
include "wne.mm"
include "cclwwlk.mm"
include "cfv.mm"
include "wcel.mm"
include "chash.mm"
include "wceq.mm"
include "wa.mm"
include "cword.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cpr.mm"
include "cmin.mm"
include "cfzo.mm"
include "wral.mm"
include "clsw.mm"
include "w3a.mm"
include "cclwwlknon.mm"
include "wb.mm"
include "c0.mm"
include "isclwwlk.mm"
include "simpl.mm"
include "fveq2.mm"
include "hash0.mm"
include "syl6eq.mm"
include "adantl.mm"
include "eqtr3d.mm"
include "ex.mm"
include "necon3d.mm"
include "impcom.mm"
include "biantrud.mm"
include "bicomd.mm"
include "3anbi1d.mm"
include "syl5bb.mm"
include "a1d.mm"
include "expimpd.mm"
include "pm5.32rd.mm"
include "cclwwlkn.mm"
include "isclwwlknon.mm"
include "isclwwlkn.mm"
include "anbi1i.mm"
include "anass.mm"
include "3bitri.mm"
include "3anass.mm"
include "3bitr4g.mm"

theorem clwwlknonel
  let vi: setvar i
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  assume clwwlknonel.v: |- V = ( Vtx ` G )
  assume clwwlknonel.e: |- E = ( Edg ` G )

  disjoint G i
  disjoint W i
  assert |- ( N =/= 0 -> ( W e. ( X ( ClWWalksNOn ` G ) N ) <-> ( ( W e. Word V /\ A. i e. ( 0 ..^ ( ( # ` W ) - 1 ) ) { ( W ` i ) , ( W ` ( i + 1 ) ) } e. E /\ { ( lastS ` W ) , ( W ` 0 ) } e. E ) /\ ( # ` W ) = N /\ ( W ` 0 ) = X ) ) )

  proof
    cN
    cc0
    wne
    #
    cW
    cG
    cclwwlk
    cfv
    wcel
    #
    cW
    chash
    cfv
    #
    cN
    wceq
    #
    cc0
    cW
    cfv
    #
    cX
    wceq
    #
    wa
    #
    wa
    #
    cW
    cV
    cword
    wcel
    #
    vi
    cv
    #
    cW
    cfv
    @9
    c1
    caddc
    co
    cW
    cfv
    cpr
    cE
    wcel
    vi
    cc0
    @2
    c1
    cmin
    co
    cfzo
    co
    wral
    #
    cW
    clsw
    cfv
    @4
    cpr
    cE
    wcel
    #
    w3a
    #
    @6
    wa
    cW
    cX
    cN
    cG
    cclwwlknon
    cfv
    co
    wcel
    #
    @12
    @3
    @5
    w3a
    @0
    @6
    @1
    @12
    @0
    @3
    @5
    @1
    @12
    wb
    #
    @0
    @3
    wa
    #
    @14
    @5
    @1
    @8
    cW
    c0
    wne
    #
    wa
    #
    @10
    @11
    w3a
    @15
    @12
    vi
    cE
    cG
    cV
    cW
    clwwlknonel.v
    clwwlknonel.e
    isclwwlk
    @15
    @17
    @8
    @10
    @11
    @15
    @8
    @17
    @15
    @16
    @8
    @3
    @0
    @16
    @3
    cW
    c0
    cN
    cc0
    @3
    cW
    c0
    wceq
    #
    cN
    cc0
    wceq
    @3
    @18
    wa
    @2
    cN
    cc0
    @3
    @18
    simpl
    @18
    @2
    cc0
    wceq
    @3
    @18
    @2
    c0
    chash
    cfv
    cc0
    cW
    c0
    chash
    fveq2
    hash0
    syl6eq
    adantl
    eqtr3d
    ex
    necon3d
    impcom
    biantrud
    bicomd
    3anbi1d
    syl5bb
    a1d
    expimpd
    pm5.32rd
    @13
    cW
    cN
    cG
    cclwwlkn
    co
    wcel
    #
    @5
    wa
    @1
    @3
    wa
    #
    @5
    wa
    @7
    cG
    cN
    cW
    cX
    isclwwlknon
    @19
    @20
    @5
    cG
    cN
    cW
    isclwwlkn
    anbi1i
    @1
    @3
    @5
    anass
    3bitri
    @12
    @3
    @5
    3anass
    3bitr4g
end
