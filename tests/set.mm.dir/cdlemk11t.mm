include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "wrex.mm"
include "csb.mm"
include "ccnv.mm"
include "ccom.mm"
include "co.mm"
include "simp11l.mm"
include "simp11r.mm"
include "cdlemftr3.mm"
include "syl2anc.mm"
include "nfv.mm"
include "nfcv.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "nfra1.mm"
include "nfriota.mm"
include "nfcxfr.mm"
include "nfcsb.mm"
include "nffv.mm"
include "nfov.mm"
include "nfbr.mm"
include "simp11.mm"
include "simp12.mm"
include "simp2.mm"
include "simp3l.mm"
include "simp3r1.mm"
include "simp3r2.mm"
include "3jca.mm"
include "simp13l.mm"
include "simp13r.mm"
include "simp3r3.mm"
include "cdlemk11tc.mm"
include "syl113anc.mm"
include "3exp.mm"
include "rexlimd.mm"
include "mpd.mm"

theorem cdlemk11t
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cW: class W
  let cX: class X
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
  assume cdlemk5.x: |- X = ( iota_ z e. T A. b e. T ( ( b =/= ( _I |` B ) /\ ( R ` b ) =/= ( R ` F ) /\ ( R ` b ) =/= ( R ` g ) ) -> ( z ` P ) = Y ) )

  disjoint ./\ g
  disjoint .\/ g
  disjoint B g
  disjoint P g
  disjoint R g
  disjoint T g
  disjoint Z g
  disjoint b g
  disjoint G g
  disjoint b z
  disjoint ./\ b
  disjoint ./\ z
  disjoint .<_ b
  disjoint g z
  disjoint .<_ g
  disjoint .<_ z
  disjoint .\/ b
  disjoint .\/ z
  disjoint A b
  disjoint A g
  disjoint A z
  disjoint B b
  disjoint B z
  disjoint F b
  disjoint F g
  disjoint F z
  disjoint G z
  disjoint H b
  disjoint H g
  disjoint H z
  disjoint K b
  disjoint K g
  disjoint K z
  disjoint N b
  disjoint N g
  disjoint N z
  disjoint P b
  disjoint P z
  disjoint R b
  disjoint R z
  disjoint T b
  disjoint T z
  disjoint W b
  disjoint W g
  disjoint W z
  disjoint Y z
  disjoint G b
  disjoint I b
  disjoint I g
  disjoint I z
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ F =/= ( _I |` B ) ) /\ ( G e. T /\ G =/= ( _I |` B ) ) ) /\ ( N e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( I e. T /\ I =/= ( _I |` B ) ) ) -> ( [_ G / g ]_ X ` P ) .<_ ( ( [_ I / g ]_ X ` P ) .\/ ( R ` ( I o. `' G ) ) ) )

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
    cF
    cT
    wcel
    cF
    cid
    cB
    cres
    #
    wne
    wa
    #
    cG
    cT
    wcel
    cG
    @2
    wne
    wa
    #
    w3a
    #
    cN
    cT
    wcel
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    cF
    cR
    cfv
    #
    cN
    cR
    cfv
    wceq
    w3a
    #
    cI
    cT
    wcel
    #
    cI
    @2
    wne
    #
    wa
    #
    w3a
    #
    vb
    cv
    #
    @2
    wne
    #
    @12
    cR
    cfv
    #
    @6
    wne
    #
    @14
    cG
    cR
    cfv
    #
    wne
    #
    @14
    cI
    cR
    cfv
    #
    wne
    #
    w3a
    #
    wa
    #
    vb
    cT
    wrex
    #
    cP
    vg
    cG
    cX
    csb
    #
    cfv
    #
    cP
    vg
    cI
    cX
    csb
    #
    cfv
    #
    cI
    cG
    ccnv
    ccom
    cR
    cfv
    #
    c.or
    co
    #
    c.le
    wbr
    #
    @11
    @0
    @1
    @22
    @0
    @1
    @3
    @4
    @7
    @10
    simp11l
    @0
    @1
    @3
    @4
    @7
    @10
    simp11r
    cB
    cR
    cT
    vb
    cH
    cK
    cW
    @6
    @16
    @18
    cdlemk5.b
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    cdlemftr3
    syl2anc
    @11
    @21
    @29
    vb
    cT
    @11
    vb
    nfv
    vb
    @24
    @28
    c.le
    vb
    cP
    @23
    vb
    vg
    cG
    cX
    vb
    cG
    nfcv
    vb
    cX
    @13
    @15
    @14
    vg
    cv
    cR
    cfv
    wne
    w3a
    cP
    vz
    cv
    cfv
    cY
    wceq
    wi
    #
    vb
    cT
    wral
    #
    vz
    cT
    crio
    cdlemk5.x
    @31
    vb
    vz
    cT
    @30
    vb
    cT
    nfra1
    vb
    cT
    nfcv
    nfriota
    nfcxfr
    #
    nfcsb
    vb
    cP
    nfcv
    #
    nffv
    vb
    c.le
    nfcv
    vb
    @26
    @27
    c.or
    vb
    cP
    @25
    vb
    vg
    cI
    cX
    vb
    cI
    nfcv
    @32
    nfcsb
    @33
    nffv
    vb
    c.or
    nfcv
    vb
    @27
    nfcv
    nfov
    nfbr
    @11
    @12
    cT
    wcel
    #
    @21
    @29
    @11
    @34
    @21
    w3a
    #
    @5
    @7
    @34
    @13
    @15
    @17
    w3a
    @8
    @9
    @19
    w3a
    @29
    @5
    @7
    @10
    @34
    @21
    simp11
    @5
    @7
    @10
    @34
    @21
    simp12
    @11
    @34
    @21
    simp2
    @35
    @13
    @15
    @17
    @11
    @34
    @13
    @20
    simp3l
    @15
    @17
    @19
    @13
    @11
    @34
    simp3r1
    @15
    @17
    @19
    @13
    @11
    @34
    simp3r2
    3jca
    @35
    @8
    @9
    @19
    @8
    @9
    @5
    @7
    @34
    @21
    simp13l
    @8
    @9
    @5
    @7
    @34
    @21
    simp13r
    @15
    @17
    @19
    @13
    @11
    @34
    simp3r3
    3jca
    vz
    cA
    cB
    cP
    cR
    cT
    vg
    cF
    cG
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cN
    cW
    cX
    cY
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
    cdlemk5.y
    cdlemk5.x
    cdlemk11tc
    syl113anc
    3exp
    rexlimd
    mpd
end
