include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "cv.mm"
include "w3a.mm"
include "cfv.mm"
include "wbr.mm"
include "wn.mm"
include "csb.mm"
include "co.mm"
include "ccnv.mm"
include "ccom.mm"
include "simp22.mm"
include "cdlemk41.mm"
include "syl.mm"
include "simp1.mm"
include "simp21l.mm"
include "simp21r.mm"
include "simp23l.mm"
include "simp31.mm"
include "simp33.mm"
include "cdlemkfid2N.mm"
include "syl132anc.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "simp1l.mm"
include "simp23r.mm"
include "simp32.mm"
include "necomd.mm"
include "cdlemkfid1N.mm"
include "3eqtrd.mm"

theorem cdlemkfid3N
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cW: class W
  let cY: class Y
  let cZ: class Z
  let vb: setvar b
  assume cdlemk5.b: |- B = ( Base ` K )
  assume cdlemk5.l: |- .<_ = ( le ` K )
  assume cdlemk5.j: |- .\/ = ( join ` K )
  assume cdlemk5.m: |- ./\ = ( meet ` K )
  assume cdlemk5.a: |- A = ( Atoms ` K )
  assume cdlemk5.h: |- H = ( LHyp ` K )
  assume cdlemk5.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk5.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemk5.z: |- Z = ( ( P .\/ ( R ` b ) ) ./\ ( ( N ` P ) .\/ ( R ` ( b o. `' F ) ) ) )
  assume cdlemk5.y: |- Y = ( ( P .\/ ( R ` g ) ) ./\ ( Z .\/ ( R ` ( g o. `' b ) ) ) )

  disjoint ./\ g
  disjoint .\/ g
  disjoint B g
  disjoint P g
  disjoint R g
  disjoint T g
  disjoint Z g
  disjoint b g
  disjoint G g
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F = N ) /\ ( ( F e. T /\ F =/= ( _I |` B ) ) /\ G e. T /\ ( b e. T /\ b =/= ( _I |` B ) ) ) /\ ( ( R ` b ) =/= ( R ` F ) /\ ( R ` b ) =/= ( R ` G ) /\ ( P e. A /\ -. P .<_ W ) ) ) -> [_ G / g ]_ Y = ( G ` P ) )

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
    cN
    wceq
    #
    wa
    #
    cF
    cT
    wcel
    #
    cF
    cid
    cB
    cres
    #
    wne
    #
    wa
    #
    cG
    cT
    wcel
    #
    vb
    cv
    #
    cT
    wcel
    #
    @8
    @4
    wne
    #
    wa
    #
    w3a
    #
    @8
    cR
    cfv
    #
    cF
    cR
    cfv
    wne
    #
    @13
    cG
    cR
    cfv
    #
    wne
    #
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    w3a
    #
    vg
    cG
    cY
    csb
    #
    cP
    @15
    c.or
    co
    #
    cZ
    cG
    @8
    ccnv
    ccom
    cR
    cfv
    #
    c.or
    co
    #
    c.an
    co
    #
    @21
    cP
    @8
    cfv
    #
    @22
    c.or
    co
    #
    c.an
    co
    #
    cP
    cG
    cfv
    #
    @19
    @7
    @20
    @24
    wceq
    @2
    @6
    @7
    @11
    @18
    simp22
    #
    cP
    cR
    cT
    vg
    cG
    c.or
    c.an
    cY
    cZ
    vb
    cdlemk5.y
    cdlemk41
    syl
    @19
    @23
    @26
    @21
    c.an
    @19
    cZ
    @25
    @22
    c.or
    @19
    @2
    @3
    @5
    @9
    @14
    @17
    cZ
    @25
    wceq
    @2
    @12
    @18
    simp1
    @3
    @5
    @7
    @11
    @2
    @18
    simp21l
    @3
    @5
    @7
    @11
    @2
    @18
    simp21r
    @9
    @10
    @6
    @7
    @2
    @18
    simp23l
    #
    @2
    @12
    @14
    @16
    @17
    simp31
    @2
    @12
    @14
    @16
    @17
    simp33
    #
    cA
    cB
    cP
    cR
    cT
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cW
    cZ
    vb
    cdlemk5.b
    cdlemk5.l
    cdlemk5.j
    cdlemk5.m
    cdlemk5.a
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    cdlemk5.z
    cdlemkfid2N
    syl132anc
    oveq1d
    oveq2d
    @19
    @0
    @9
    @10
    @7
    @15
    @13
    wne
    @17
    @27
    @28
    wceq
    @0
    @1
    @12
    @18
    simp1l
    @30
    @9
    @10
    @6
    @7
    @2
    @18
    simp23r
    @29
    @19
    @13
    @15
    @2
    @12
    @14
    @16
    @17
    simp32
    necomd
    @31
    cA
    cB
    cP
    cR
    cT
    @8
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemk5.b
    cdlemk5.l
    cdlemk5.j
    cdlemk5.m
    cdlemk5.a
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    cdlemkfid1N
    syl132anc
    3eqtrd
end
