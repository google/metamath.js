include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "clat.mm"
include "claut.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "eqid.mm"
include "ltrnlaut.mm"
include "3adant3.mm"
include "simp3l.mm"
include "simp3r.mm"
include "lautj.mm"
include "syl13anc.mm"

theorem ltrnj
  let cB: class B
  let cT: class T
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  assume ltrnj.b: |- B = ( Base ` K )
  assume ltrnj.j: |- .\/ = ( join ` K )
  assume ltrnj.h: |- H = ( LHyp ` K )
  assume ltrnj.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ ( X e. B /\ Y e. B ) ) -> ( F ` ( X .\/ Y ) ) = ( ( F ` X ) .\/ ( F ` Y ) ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cF
    cT
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
    wa
    #
    w3a
    #
    cK
    clat
    wcel
    #
    cF
    cK
    claut
    cfv
    #
    wcel
    #
    @4
    @5
    cX
    cY
    c.or
    co
    cF
    cfv
    cX
    cF
    cfv
    cY
    cF
    cfv
    c.or
    co
    wceq
    @7
    @0
    @8
    @0
    @1
    @3
    @6
    simp1l
    cK
    hllat
    syl
    @2
    @3
    @10
    @6
    cT
    cF
    cH
    @9
    cK
    chlt
    cW
    ltrnj.h
    @9
    eqid
    #
    ltrnj.t
    ltrnlaut
    3adant3
    @2
    @3
    @4
    @5
    simp3l
    @2
    @3
    @4
    @5
    simp3r
    cB
    cF
    @9
    c.or
    cK
    cX
    cY
    ltrnj.b
    ltrnj.j
    @11
    lautj
    syl13anc
end
