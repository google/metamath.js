include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "cid.mm"
include "cres.mm"
include "cv.mm"
include "wne.mm"
include "csb.mm"
include "simp32.mm"
include "csbeq1d.mm"
include "co.mm"
include "ccnv.mm"
include "ccom.mm"
include "idltrn.mm"
include "3ad2ant1.mm"
include "cdlemk41.mm"
include "syl.mm"
include "cp0.mm"
include "eqid.mm"
include "trlid0.mm"
include "oveq2d.mm"
include "col.mm"
include "simp1l.mm"
include "hlol.mm"
include "simp31l.mm"
include "atbase.mm"
include "olj01.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "wf1o.mm"
include "wf.mm"
include "simp1.mm"
include "simp33l.mm"
include "ltrncnv.mm"
include "ltrn1o.mm"
include "f1of.mm"
include "fcoi2.mm"
include "3syl.mm"
include "fveq2d.mm"
include "trlcnv.mm"
include "simp31.mm"
include "simp33.mm"
include "jca.mm"
include "cdlemkid1.mm"
include "syld3an3.mm"
include "oveq12d.mm"
include "clat.mm"
include "hllat.mm"
include "trlcl.mm"
include "latabs2.mm"
include "syl3anc.mm"

theorem cdlemkid2
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ N e. T /\ ( R ` F ) = ( R ` N ) ) /\ ( ( P e. A /\ -. P .<_ W ) /\ G = ( _I |` B ) /\ ( b e. T /\ b =/= ( _I |` B ) ) ) ) -> [_ G / g ]_ Y = P )

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
    cN
    cT
    wcel
    cF
    cR
    cfv
    cN
    cR
    cfv
    wceq
    w3a
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
    cG
    cid
    cB
    cres
    #
    wceq
    #
    vb
    cv
    #
    cT
    wcel
    #
    @9
    @7
    wne
    #
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
    vg
    @7
    cY
    csb
    #
    cP
    @14
    vg
    cG
    @7
    cY
    @2
    @3
    @6
    @8
    @12
    simp32
    csbeq1d
    @14
    @15
    cP
    @7
    cR
    cfv
    #
    c.or
    co
    #
    cZ
    @7
    @9
    ccnv
    #
    ccom
    #
    cR
    cfv
    #
    c.or
    co
    #
    c.an
    co
    #
    cP
    @14
    @7
    cT
    wcel
    #
    @15
    @22
    wceq
    @2
    @3
    @23
    @13
    cB
    cT
    cH
    cK
    cW
    cdlemk5.b
    cdlemk5.h
    cdlemk5.t
    idltrn
    3ad2ant1
    cP
    cR
    cT
    vg
    @7
    c.or
    c.an
    cY
    cZ
    vb
    cdlemk5.y
    cdlemk41
    syl
    @14
    @22
    cP
    cP
    @9
    cR
    cfv
    #
    c.or
    co
    #
    c.an
    co
    #
    cP
    @14
    @17
    cP
    @21
    @25
    c.an
    @14
    @17
    cP
    cK
    cp0
    cfv
    #
    c.or
    co
    #
    cP
    @14
    @16
    @27
    cP
    c.or
    @2
    @3
    @16
    @27
    wceq
    @13
    cB
    cR
    cH
    cK
    cW
    @27
    cdlemk5.b
    @27
    eqid
    #
    cdlemk5.h
    cdlemk5.r
    trlid0
    3ad2ant1
    oveq2d
    @14
    cK
    col
    wcel
    #
    cP
    cB
    wcel
    #
    @28
    cP
    wceq
    @14
    @0
    @30
    @0
    @1
    @3
    @13
    simp1l
    #
    cK
    hlol
    syl
    @14
    @4
    @31
    @4
    @5
    @8
    @12
    @2
    @3
    simp31l
    cA
    cB
    cP
    cK
    cdlemk5.b
    cdlemk5.a
    atbase
    syl
    #
    cB
    c.or
    cK
    cP
    @27
    cdlemk5.b
    cdlemk5.j
    @29
    olj01
    syl2anc
    eqtrd
    @14
    @21
    cZ
    @24
    c.or
    co
    #
    @25
    @14
    @20
    @24
    cZ
    c.or
    @14
    @20
    @18
    cR
    cfv
    #
    @24
    @14
    @19
    @18
    cR
    @14
    cB
    cB
    @18
    wf1o
    #
    cB
    cB
    @18
    wf
    @19
    @18
    wceq
    @14
    @2
    @18
    cT
    wcel
    #
    @36
    @2
    @3
    @13
    simp1
    #
    @14
    @2
    @10
    @37
    @38
    @10
    @11
    @6
    @8
    @2
    @3
    simp33l
    #
    cT
    @9
    cH
    cK
    cW
    cdlemk5.h
    cdlemk5.t
    ltrncnv
    syl2anc
    cB
    cT
    @18
    cH
    cK
    chlt
    cW
    cdlemk5.b
    cdlemk5.h
    cdlemk5.t
    ltrn1o
    syl2anc
    cB
    cB
    @18
    f1of
    cB
    cB
    @18
    fcoi2
    3syl
    fveq2d
    @14
    @2
    @10
    @35
    @24
    wceq
    @38
    @39
    cR
    cT
    @9
    cH
    cK
    cW
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    trlcnv
    syl2anc
    eqtrd
    oveq2d
    @2
    @3
    @13
    @6
    @12
    wa
    @34
    @25
    wceq
    @14
    @6
    @12
    @2
    @3
    @6
    @8
    @12
    simp31
    @2
    @3
    @6
    @8
    @12
    simp33
    jca
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
    cdlemkid1
    syld3an3
    eqtrd
    oveq12d
    @14
    cK
    clat
    wcel
    #
    @31
    @24
    cB
    wcel
    #
    @26
    cP
    wceq
    @14
    @0
    @40
    @32
    cK
    hllat
    syl
    @33
    @14
    @2
    @10
    @41
    @38
    @39
    cB
    cR
    cT
    @9
    cH
    cK
    cW
    cdlemk5.b
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    trlcl
    syl2anc
    cB
    c.or
    cK
    c.an
    cP
    @24
    cdlemk5.b
    cdlemk5.j
    cdlemk5.m
    latabs2
    syl3anc
    eqtrd
    eqtrd
    eqtrd
end
