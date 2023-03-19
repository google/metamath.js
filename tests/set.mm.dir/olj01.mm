include "col.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "cops.mm"
include "olop.mm"
include "op0cl.mm"
include "syl.mm"
include "adantr.mm"
include "w3a.mm"
include "cple.mm"
include "cfv.mm"
include "eqid.mm"
include "clat.mm"
include "ollat.mm"
include "3ad2ant1.mm"
include "latjcl.mm"
include "syl3an1.mm"
include "simp2.mm"
include "wbr.mm"
include "latref.mm"
include "sylan.mm"
include "3adant3.mm"
include "op0le.mm"
include "wa.mm"
include "wb.mm"
include "simp3.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "latlej1.mm"
include "latasymd.mm"
include "mpd3an3.mm"

theorem olj01
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let cX: class X
  let c.0: class .0.
  assume olj0.b: |- B = ( Base ` K )
  assume olj0.j: |- .\/ = ( join ` K )
  assume olj0.z: |- .0. = ( 0. ` K )


  assert |- ( ( K e. OL /\ X e. B ) -> ( X .\/ .0. ) = X )

  proof
    cK
    col
    wcel
    #
    cX
    cB
    wcel
    #
    c.0
    cB
    wcel
    #
    cX
    c.0
    c.or
    co
    #
    cX
    wceq
    @0
    @2
    @1
    @0
    cK
    cops
    wcel
    #
    @2
    cK
    olop
    #
    cB
    cK
    c.0
    olj0.b
    olj0.z
    op0cl
    syl
    adantr
    @0
    @1
    @2
    w3a
    #
    cB
    cK
    cK
    cple
    cfv
    #
    @3
    cX
    olj0.b
    @7
    eqid
    #
    @0
    @1
    cK
    clat
    wcel
    #
    @2
    cK
    ollat
    #
    3ad2ant1
    #
    @0
    @9
    @1
    @2
    @3
    cB
    wcel
    @10
    cB
    c.or
    cK
    cX
    c.0
    olj0.b
    olj0.j
    latjcl
    syl3an1
    @0
    @1
    @2
    simp2
    #
    @6
    cX
    cX
    @7
    wbr
    #
    c.0
    cX
    @7
    wbr
    #
    @3
    cX
    @7
    wbr
    #
    @0
    @1
    @13
    @2
    @0
    @9
    @1
    @13
    @10
    cB
    cK
    @7
    cX
    olj0.b
    @8
    latref
    sylan
    3adant3
    @0
    @1
    @14
    @2
    @0
    @4
    @1
    @14
    @5
    cB
    cK
    @7
    cX
    c.0
    olj0.b
    @8
    olj0.z
    op0le
    sylan
    3adant3
    @6
    @9
    @1
    @2
    @1
    @13
    @14
    wa
    @15
    wb
    @11
    @12
    @0
    @1
    @2
    simp3
    @12
    cB
    c.or
    cK
    @7
    cX
    c.0
    cX
    olj0.b
    @8
    olj0.j
    latjle12
    syl13anc
    mpbi2and
    @0
    @9
    @1
    @2
    cX
    @3
    @7
    wbr
    @10
    cB
    c.or
    cK
    @7
    cX
    c.0
    olj0.b
    @8
    olj0.j
    latlej1
    syl3an1
    latasymd
    mpd3an3
end
