include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "ccom.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "ltrncoval.mm"
include "3adant3r.mm"
include "oveq1d.mm"
include "simp1.mm"
include "simp2l.mm"
include "ltrnel.mm"
include "3adant2l.mm"
include "trljat3.mm"
include "syl3anc.mm"
include "eqtr4d.mm"

theorem trlcoabs
  let cA: class A
  let cP: class P
  let cR: class R
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume trlcoabs.l: |- .<_ = ( le ` K )
  assume trlcoabs.j: |- .\/ = ( join ` K )
  assume trlcoabs.a: |- A = ( Atoms ` K )
  assume trlcoabs.h: |- H = ( LHyp ` K )
  assume trlcoabs.t: |- T = ( ( LTrn ` K ) ` W )
  assume trlcoabs.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ G e. T ) /\ ( P e. A /\ -. P .<_ W ) ) -> ( ( ( F o. G ) ` P ) .\/ ( R ` F ) ) = ( ( G ` P ) .\/ ( R ` F ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
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
    wa
    #
    cP
    cA
    wcel
    #
    cP
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    cP
    cF
    cG
    ccom
    cfv
    #
    cF
    cR
    cfv
    #
    c.or
    co
    cP
    cG
    cfv
    #
    cF
    cfv
    #
    @9
    c.or
    co
    #
    @10
    @9
    c.or
    co
    #
    @7
    @8
    @11
    @9
    c.or
    @0
    @3
    @4
    @8
    @11
    wceq
    @5
    cA
    cP
    cT
    cF
    cG
    cH
    cK
    c.le
    cW
    trlcoabs.l
    trlcoabs.a
    trlcoabs.h
    trlcoabs.t
    ltrncoval
    3adant3r
    oveq1d
    @7
    @0
    @1
    @10
    cA
    wcel
    @10
    cW
    c.le
    wbr
    wn
    wa
    #
    @13
    @12
    wceq
    @0
    @3
    @6
    simp1
    @0
    @1
    @2
    @6
    simp2l
    @0
    @2
    @6
    @14
    @1
    cA
    cP
    cT
    cG
    cH
    cK
    c.le
    cW
    trlcoabs.l
    trlcoabs.a
    trlcoabs.h
    trlcoabs.t
    ltrnel
    3adant2l
    cA
    @10
    cR
    cT
    cF
    cH
    c.or
    cK
    c.le
    cW
    trlcoabs.l
    trlcoabs.j
    trlcoabs.a
    trlcoabs.h
    trlcoabs.t
    trlcoabs.r
    trljat3
    syl3anc
    eqtr4d
end
