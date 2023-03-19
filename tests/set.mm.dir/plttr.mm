include "cpo.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wbr.mm"
include "cple.mm"
include "cfv.mm"
include "wne.mm"
include "wi.mm"
include "eqid.mm"
include "pltle.mm"
include "3adant3r3.mm"
include "3adant3r1.mm"
include "postr.mm"
include "syl2and.mm"
include "wn.mm"
include "wceq.mm"
include "pltn2lp.mm"
include "breq2.mm"
include "anbi2d.mm"
include "notbid.mm"
include "syl5ibcom.mm"
include "necon2ad.mm"
include "jcad.mm"
include "wb.mm"
include "pltval.mm"
include "3adant3r2.mm"
include "sylibrd.mm"

theorem plttr
  let cB: class B
  let c.lt: class .<
  let cK: class K
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume pltnlt.b: |- B = ( Base ` K )
  assume pltnlt.s: |- .< = ( lt ` K )


  assert |- ( ( K e. Poset /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X .< Y /\ Y .< Z ) -> X .< Z ) )

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
    wa
    #
    cX
    cY
    c.lt
    wbr
    #
    cY
    cZ
    c.lt
    wbr
    #
    wa
    #
    cX
    cZ
    cK
    cple
    cfv
    #
    wbr
    #
    cX
    cZ
    wne
    #
    wa
    #
    cX
    cZ
    c.lt
    wbr
    #
    @4
    @7
    @9
    @10
    @4
    @5
    cX
    cY
    @8
    wbr
    #
    @6
    cY
    cZ
    @8
    wbr
    #
    @9
    @0
    @1
    @2
    @5
    @13
    wi
    @3
    cpo
    cB
    cB
    c.lt
    cK
    @8
    cX
    cY
    @8
    eqid
    #
    pltnlt.s
    pltle
    3adant3r3
    @0
    @2
    @3
    @6
    @14
    wi
    @1
    cpo
    cB
    cB
    c.lt
    cK
    @8
    cY
    cZ
    @15
    pltnlt.s
    pltle
    3adant3r1
    cB
    cK
    @8
    cX
    cY
    cZ
    pltnlt.b
    @15
    postr
    syl2and
    @4
    @7
    cX
    cZ
    @4
    @5
    cY
    cX
    c.lt
    wbr
    #
    wa
    #
    wn
    #
    cX
    cZ
    wceq
    #
    @7
    wn
    @0
    @1
    @2
    @18
    @3
    cB
    c.lt
    cK
    cX
    cY
    pltnlt.b
    pltnlt.s
    pltn2lp
    3adant3r3
    @19
    @17
    @7
    @19
    @16
    @6
    @5
    cX
    cZ
    cY
    c.lt
    breq2
    anbi2d
    notbid
    syl5ibcom
    necon2ad
    jcad
    @0
    @1
    @3
    @12
    @11
    wb
    @2
    cpo
    cB
    cB
    c.lt
    cK
    @8
    cX
    cZ
    @15
    pltnlt.s
    pltval
    3adant3r2
    sylibrd
end
