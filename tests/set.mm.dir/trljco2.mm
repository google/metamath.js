include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "ccom.mm"
include "clat.mm"
include "cbs.mm"
include "wceq.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "eqid.mm"
include "trlcl.mm"
include "3adant3.mm"
include "3adant2.mm"
include "latjcom.mm"
include "syl3anc.mm"
include "trljco.mm"
include "3com23.mm"
include "eqtr4d.mm"
include "ltrncom.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"

theorem trljco2
  let cR: class R
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let cW: class W
  assume trljco.j: |- .\/ = ( join ` K )
  assume trljco.h: |- H = ( LHyp ` K )
  assume trljco.t: |- T = ( ( LTrn ` K ) ` W )
  assume trljco.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ G e. T ) -> ( ( R ` F ) .\/ ( R ` ( F o. G ) ) ) = ( ( R ` G ) .\/ ( R ` ( F o. G ) ) ) )

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
    cG
    cT
    wcel
    #
    w3a
    #
    cF
    cR
    cfv
    #
    cG
    cR
    cfv
    #
    c.or
    co
    #
    @7
    cG
    cF
    ccom
    #
    cR
    cfv
    #
    c.or
    co
    #
    @6
    cF
    cG
    ccom
    #
    cR
    cfv
    #
    c.or
    co
    @7
    @13
    c.or
    co
    @5
    @8
    @7
    @6
    c.or
    co
    #
    @11
    @5
    cK
    clat
    wcel
    #
    @6
    cK
    cbs
    cfv
    #
    wcel
    #
    @7
    @16
    wcel
    #
    @8
    @14
    wceq
    @5
    @0
    @15
    @0
    @1
    @3
    @4
    simp1l
    cK
    hllat
    syl
    @2
    @3
    @17
    @4
    @16
    cR
    cT
    cF
    cH
    cK
    cW
    @16
    eqid
    #
    trljco.h
    trljco.t
    trljco.r
    trlcl
    3adant3
    @2
    @4
    @18
    @3
    @16
    cR
    cT
    cG
    cH
    cK
    cW
    @19
    trljco.h
    trljco.t
    trljco.r
    trlcl
    3adant2
    @16
    c.or
    cK
    @6
    @7
    @19
    trljco.j
    latjcom
    syl3anc
    @2
    @4
    @3
    @11
    @14
    wceq
    cR
    cT
    cG
    cF
    cH
    c.or
    cK
    cW
    trljco.j
    trljco.h
    trljco.t
    trljco.r
    trljco
    3com23
    eqtr4d
    cR
    cT
    cF
    cG
    cH
    c.or
    cK
    cW
    trljco.j
    trljco.h
    trljco.t
    trljco.r
    trljco
    @5
    @13
    @10
    @7
    c.or
    @5
    @12
    @9
    cR
    cT
    cF
    cG
    cH
    cK
    cW
    trljco.h
    trljco.t
    ltrncom
    fveq2d
    oveq2d
    3eqtr4d
end
