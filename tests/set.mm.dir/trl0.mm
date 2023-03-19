include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "cjn.mm"
include "co.mm"
include "cmee.mm"
include "simp1.mm"
include "simp3l.mm"
include "simp2.mm"
include "eqid.mm"
include "trlval2.mm"
include "syl3anc.mm"
include "simp3r.mm"
include "oveq2d.mm"
include "simp1l.mm"
include "simp2l.mm"
include "hlatjidm.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "lhpmat.mm"
include "3eqtrd.mm"

theorem trl0
  let cA: class A
  let cP: class P
  let cR: class R
  let cT: class T
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let c.0: class .0.
  assume trl0.l: |- .<_ = ( le ` K )
  assume trl0.z: |- .0. = ( 0. ` K )
  assume trl0.a: |- A = ( Atoms ` K )
  assume trl0.h: |- H = ( LHyp ` K )
  assume trl0.t: |- T = ( ( LTrn ` K ) ` W )
  assume trl0.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( F e. T /\ ( F ` P ) = P ) ) -> ( R ` F ) = .0. )

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
    cF
    cT
    wcel
    #
    cP
    cF
    cfv
    #
    cP
    wceq
    #
    wa
    #
    w3a
    #
    cF
    cR
    cfv
    #
    cP
    @7
    cK
    cjn
    cfv
    #
    co
    #
    cW
    cK
    cmee
    cfv
    #
    co
    #
    cP
    cW
    @14
    co
    #
    c.0
    @10
    @2
    @6
    @5
    @11
    @15
    wceq
    @2
    @5
    @9
    simp1
    #
    @2
    @5
    @6
    @8
    simp3l
    @2
    @5
    @9
    simp2
    #
    cA
    cP
    cR
    cT
    cF
    cH
    @12
    cK
    c.le
    @14
    cW
    trl0.l
    @12
    eqid
    #
    @14
    eqid
    #
    trl0.a
    trl0.h
    trl0.t
    trl0.r
    trlval2
    syl3anc
    @10
    @13
    cP
    cW
    @14
    @10
    @13
    cP
    cP
    @12
    co
    #
    cP
    @10
    @7
    cP
    cP
    @12
    @2
    @5
    @6
    @8
    simp3r
    oveq2d
    @10
    @0
    @3
    @21
    cP
    wceq
    @0
    @1
    @5
    @9
    simp1l
    @2
    @3
    @4
    @9
    simp2l
    cA
    @12
    cK
    cP
    @19
    trl0.a
    hlatjidm
    syl2anc
    eqtrd
    oveq1d
    @10
    @2
    @5
    @16
    c.0
    wceq
    @17
    @18
    cA
    cP
    cH
    cK
    c.le
    @14
    cW
    c.0
    trl0.l
    @20
    trl0.z
    trl0.a
    trl0.h
    lhpmat
    syl2anc
    3eqtrd
end
