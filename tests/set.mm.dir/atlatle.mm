include "coml.mm"
include "wcel.mm"
include "ccla.mm"
include "cal.mm"
include "w3a.mm"
include "wbr.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "cpo.mm"
include "simpl13.mm"
include "atlpos.mm"
include "syl.mm"
include "atbase.mm"
include "adantl.mm"
include "simpl2.mm"
include "simpl3.mm"
include "postr.mm"
include "syl13anc.mm"
include "expcomd.mm"
include "ralrimdva.mm"
include "crab.mm"
include "wss.mm"
include "ss2rab.mm"
include "club.mm"
include "cfv.mm"
include "simpl12.mm"
include "ssrab2.mm"
include "atssbase.mm"
include "sstri.mm"
include "eqid.mm"
include "lubss.mm"
include "mp3an2.mm"
include "sylancom.mm"
include "ex.mm"
include "wceq.mm"
include "atlatmstc.mm"
include "3adant3.mm"
include "3adant2.mm"
include "breq12d.mm"
include "sylibd.mm"
include "syl5bir.mm"
include "impbid.mm"

theorem atlatle
  let cA: class A
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let vp: setvar p
  assume atlatle.b: |- B = ( Base ` K )
  assume atlatle.l: |- .<_ = ( le ` K )
  assume atlatle.a: |- A = ( Atoms ` K )

  disjoint A p
  disjoint B p
  disjoint K p
  disjoint .<_ p
  disjoint X p
  disjoint Y p
  assert |- ( ( ( K e. OML /\ K e. CLat /\ K e. AtLat ) /\ X e. B /\ Y e. B ) -> ( X .<_ Y <-> A. p e. A ( p .<_ X -> p .<_ Y ) ) )

  proof
    cK
    coml
    wcel
    #
    cK
    ccla
    wcel
    #
    cK
    cal
    wcel
    #
    w3a
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cX
    cY
    c.le
    wbr
    #
    vp
    cv
    #
    cX
    c.le
    wbr
    #
    @8
    cY
    c.le
    wbr
    #
    wi
    #
    vp
    cA
    wral
    #
    @6
    @7
    @11
    vp
    cA
    @6
    @8
    cA
    wcel
    #
    wa
    #
    @9
    @7
    @10
    @14
    cK
    cpo
    wcel
    #
    @8
    cB
    wcel
    #
    @4
    @5
    @9
    @7
    wa
    @10
    wi
    @14
    @2
    @15
    @0
    @1
    @2
    @4
    @5
    @13
    simpl13
    cK
    atlpos
    syl
    @13
    @16
    @6
    cA
    cB
    @8
    cK
    atlatle.b
    atlatle.a
    atbase
    adantl
    @3
    @4
    @5
    @13
    simpl2
    @3
    @4
    @5
    @13
    simpl3
    cB
    cK
    c.le
    @8
    cX
    cY
    atlatle.b
    atlatle.l
    postr
    syl13anc
    expcomd
    ralrimdva
    @12
    @9
    vp
    cA
    crab
    #
    @10
    vp
    cA
    crab
    #
    wss
    #
    @6
    @7
    @9
    @10
    vp
    cA
    ss2rab
    @6
    @19
    @17
    cK
    club
    cfv
    #
    cfv
    #
    @18
    @20
    cfv
    #
    c.le
    wbr
    #
    @7
    @6
    @19
    @23
    @6
    @19
    @1
    @23
    @0
    @1
    @2
    @4
    @5
    @19
    simpl12
    @1
    @18
    cB
    wss
    @19
    @23
    @18
    cA
    cB
    @10
    vp
    cA
    ssrab2
    cA
    cB
    cK
    atlatle.b
    atlatle.a
    atssbase
    sstri
    cB
    @17
    @18
    @20
    cK
    c.le
    atlatle.b
    atlatle.l
    @20
    eqid
    #
    lubss
    mp3an2
    sylancom
    ex
    @6
    @21
    cX
    @22
    cY
    c.le
    @3
    @4
    @21
    cX
    wceq
    @5
    vp
    cA
    cB
    @20
    cK
    c.le
    cX
    atlatle.b
    atlatle.l
    @24
    atlatle.a
    atlatmstc
    3adant3
    @3
    @5
    @22
    cY
    wceq
    @4
    vp
    cA
    cB
    @20
    cK
    c.le
    cY
    atlatle.b
    atlatle.l
    @24
    atlatle.a
    atlatmstc
    3adant2
    breq12d
    sylibd
    syl5bir
    impbid
end
