include "cpo.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "wne.mm"
include "simpl1.mm"
include "simpl23.mm"
include "simpl21.mm"
include "simpl3l.mm"
include "cvrne.mm"
include "syl31anc.mm"
include "wo.mm"
include "wi.mm"
include "cvrle.mm"
include "simpr.mm"
include "wb.mm"
include "simpl22.mm"
include "simpl3r.mm"
include "cvrnbtwn4.mm"
include "syl131anc.mm"
include "mpbi2and.mm"
include "neor.mm"
include "sylib.mm"
include "mpd.mm"
include "ex.mm"
include "simp1.mm"
include "simp21.mm"
include "posref.mm"
include "syl2anc.mm"
include "breq2.mm"
include "syl5ibcom.mm"
include "impbid.mm"

theorem cvrcmp
  let cB: class B
  let cC: class C
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume cvrcmp.b: |- B = ( Base ` K )
  assume cvrcmp.l: |- .<_ = ( le ` K )
  assume cvrcmp.c: |- C = ( <o ` K )


  assert |- ( ( K e. Poset /\ ( X e. B /\ Y e. B /\ Z e. B ) /\ ( Z C X /\ Z C Y ) ) -> ( X .<_ Y <-> X = Y ) )

  proof
    cK
    cpo
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    cZ
    cB
    wcel
    #
    w3a
    #
    cZ
    cX
    cC
    wbr
    #
    cZ
    cY
    cC
    wbr
    #
    wa
    #
    w3a
    #
    cX
    cY
    c.le
    wbr
    #
    cX
    cY
    wceq
    #
    @8
    @9
    @10
    @8
    @9
    wa
    #
    cZ
    cX
    wne
    #
    @10
    @11
    @0
    @3
    @1
    @5
    @12
    @0
    @4
    @7
    @9
    simpl1
    #
    @1
    @2
    @3
    @0
    @7
    @9
    simpl23
    #
    @1
    @2
    @3
    @0
    @7
    @9
    simpl21
    #
    @5
    @6
    @0
    @4
    @9
    simpl3l
    #
    cpo
    cB
    cC
    cK
    cZ
    cX
    cvrcmp.b
    cvrcmp.c
    cvrne
    syl31anc
    @11
    cZ
    cX
    wceq
    @10
    wo
    #
    @12
    @10
    wi
    @11
    cZ
    cX
    c.le
    wbr
    #
    @9
    @17
    @11
    @0
    @3
    @1
    @5
    @18
    @13
    @14
    @15
    @16
    cpo
    cB
    cC
    cK
    c.le
    cZ
    cX
    cvrcmp.b
    cvrcmp.l
    cvrcmp.c
    cvrle
    syl31anc
    @8
    @9
    simpr
    @11
    @0
    @3
    @2
    @1
    @6
    @18
    @9
    wa
    @17
    wb
    @13
    @14
    @1
    @2
    @3
    @0
    @7
    @9
    simpl22
    @15
    @5
    @6
    @0
    @4
    @9
    simpl3r
    cB
    cC
    cK
    c.le
    cZ
    cY
    cX
    cvrcmp.b
    cvrcmp.l
    cvrcmp.c
    cvrnbtwn4
    syl131anc
    mpbi2and
    @10
    cZ
    cX
    neor
    sylib
    mpd
    ex
    @8
    cX
    cX
    c.le
    wbr
    #
    @10
    @9
    @8
    @0
    @1
    @19
    @0
    @4
    @7
    simp1
    @0
    @1
    @2
    @3
    @7
    simp21
    cB
    cK
    c.le
    cX
    cvrcmp.b
    cvrcmp.l
    posref
    syl2anc
    cX
    cY
    cX
    c.le
    breq2
    syl5ibcom
    impbid
end
