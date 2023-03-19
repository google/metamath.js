include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "wrex.mm"
include "csb.mm"
include "simp1l.mm"
include "cdlemftr1.mm"
include "syl.mm"
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
include "nfeq1.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simpr.mm"
include "cdlemk19xlem.mm"
include "syl121anc.mm"
include "exp32.mm"
include "rexlimd.mm"
include "mpd.mm"

theorem cdlemk19x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let vg: setvar g
  let cF: class F
  let cH: class H
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
  let cG: class G
  let cI: class I
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
  disjoint G g
  disjoint G z
  disjoint G b
  disjoint I b
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( R ` F ) = ( R ` N ) ) /\ ( F e. T /\ F =/= ( _I |` B ) /\ N e. T ) /\ ( P e. A /\ -. P .<_ W ) ) -> ( [_ F / g ]_ X ` P ) = ( N ` P ) )

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
    cR
    cfv
    #
    cN
    cR
    cfv
    wceq
    #
    wa
    #
    cF
    cT
    wcel
    cF
    cid
    cB
    cres
    #
    wne
    cN
    cT
    wcel
    w3a
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
    vb
    cv
    #
    @4
    wne
    #
    @8
    cR
    cfv
    #
    @1
    wne
    #
    wa
    #
    vb
    cT
    wrex
    #
    cP
    vg
    cF
    cX
    csb
    #
    cfv
    #
    cP
    cN
    cfv
    #
    wceq
    #
    @7
    @0
    @13
    @0
    @2
    @5
    @6
    simp1l
    cB
    cR
    cT
    vb
    cH
    cK
    cW
    @1
    cdlemk5.b
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    cdlemftr1
    syl
    @7
    @12
    @17
    vb
    cT
    @7
    vb
    nfv
    vb
    @15
    @16
    vb
    cP
    @14
    vb
    vg
    cF
    cX
    vb
    cF
    nfcv
    vb
    cX
    @9
    @11
    @10
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
    @19
    vb
    vz
    cT
    @18
    vb
    cT
    nfra1
    vb
    cT
    nfcv
    nfriota
    nfcxfr
    nfcsb
    vb
    cP
    nfcv
    nffv
    nfeq1
    @7
    @8
    cT
    wcel
    #
    @12
    @17
    @7
    @20
    @12
    wa
    #
    wa
    @3
    @5
    @6
    @21
    @17
    @3
    @5
    @6
    @21
    simpl1
    @3
    @5
    @6
    @21
    simpl2
    @3
    @5
    @6
    @21
    simpl3
    @7
    @21
    simpr
    vz
    cA
    cB
    cP
    cR
    cT
    vg
    cF
    cH
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
    cdlemk19xlem
    syl121anc
    exp32
    rexlimd
    mpd
end
