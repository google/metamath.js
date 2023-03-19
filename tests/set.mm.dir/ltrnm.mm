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
include "lautm.mm"
include "syl13anc.mm"

theorem ltrnm
  let cB: class B
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let cY: class Y
  assume ltrnm.b: |- B = ( Base ` K )
  assume ltrnm.m: |- ./\ = ( meet ` K )
  assume ltrnm.h: |- H = ( LHyp ` K )
  assume ltrnm.t: |- T = ( ( LTrn ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ ( X e. B /\ Y e. B ) ) -> ( F ` ( X ./\ Y ) ) = ( ( F ` X ) ./\ ( F ` Y ) ) )

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
    c.an
    co
    cF
    cfv
    cX
    cF
    cfv
    cY
    cF
    cfv
    c.an
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
    ltrnm.h
    @9
    eqid
    #
    ltrnm.t
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
    cK
    c.an
    cX
    cY
    ltrnm.b
    ltrnm.m
    @11
    lautm
    syl13anc
end
