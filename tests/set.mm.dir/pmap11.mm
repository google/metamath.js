include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wceq.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "cple.mm"
include "wbr.mm"
include "clat.mm"
include "wb.mm"
include "hllat.mm"
include "eqid.mm"
include "latasymb.mm"
include "syl3an1.mm"
include "pmaple.mm"
include "3com23.mm"
include "anbi12d.mm"
include "bitr3d.mm"
include "eqss.mm"
include "syl6rbbr.mm"

theorem pmap11
  let cB: class B
  let cK: class K
  let cM: class M
  let cX: class X
  let cY: class Y
  assume pmap11.b: |- B = ( Base ` K )
  assume pmap11.m: |- M = ( pmap ` K )


  assert |- ( ( K e. HL /\ X e. B /\ Y e. B ) -> ( ( M ` X ) = ( M ` Y ) <-> X = Y ) )

  proof
    cK
    chlt
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
    w3a
    #
    cX
    cY
    wceq
    #
    cX
    cM
    cfv
    #
    cY
    cM
    cfv
    #
    wss
    #
    @6
    @5
    wss
    #
    wa
    #
    @5
    @6
    wceq
    @3
    cX
    cY
    cK
    cple
    cfv
    #
    wbr
    #
    cY
    cX
    @10
    wbr
    #
    wa
    #
    @4
    @9
    @0
    cK
    clat
    wcel
    @1
    @2
    @13
    @4
    wb
    cK
    hllat
    cB
    cK
    @10
    cX
    cY
    pmap11.b
    @10
    eqid
    #
    latasymb
    syl3an1
    @3
    @11
    @7
    @12
    @8
    cB
    cK
    @10
    cM
    cX
    cY
    pmap11.b
    @14
    pmap11.m
    pmaple
    @0
    @2
    @1
    @12
    @8
    wb
    cB
    cK
    @10
    cM
    cY
    cX
    pmap11.b
    @14
    pmap11.m
    pmaple
    3com23
    anbi12d
    bitr3d
    @5
    @6
    eqss
    syl6rbbr
end
