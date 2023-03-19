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
include "cvv.mm"
include "csb.mm"
include "cltrn.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cv.mm"
include "wne.mm"
include "nfv.mm"
include "wnf.mm"
include "nfcv.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "nfra1.mm"
include "nfriota.mm"
include "nfcxfr.mm"
include "nfcsb.mm"
include "nfeq1.mm"
include "a1i.mm"
include "cdlemkid4.mm"
include "wb.mm"
include "eqeq1.mm"
include "adantl.mm"
include "eqidd.mm"
include "cdlemkid5.mm"
include "wrex.mm"
include "cdlemftr2.mm"
include "3ad2ant1.mm"
include "riotasv3d.mm"
include "mpan2.mm"

theorem cdlemkid
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ N e. T /\ ( R ` F ) = ( R ` N ) ) /\ ( ( P e. A /\ -. P .<_ W ) /\ G = ( _I |` B ) ) ) -> [_ G / g ]_ X = ( _I |` B ) )

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
    cN
    cT
    wcel
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
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    cG
    cid
    cB
    cres
    #
    wceq
    wa
    #
    w3a
    #
    cT
    cvv
    wcel
    vg
    cG
    cX
    csb
    #
    @3
    wceq
    #
    cT
    cW
    cK
    cltrn
    cfv
    #
    cfv
    cvv
    cdlemk5.t
    cW
    @8
    fvex
    eqeltri
    @5
    vb
    cv
    #
    @3
    wne
    #
    @9
    cR
    cfv
    #
    @1
    wne
    #
    @11
    cG
    cR
    cfv
    #
    wne
    w3a
    #
    @3
    @3
    wceq
    #
    @7
    vz
    vb
    cT
    cT
    @3
    @6
    cvv
    @5
    vb
    nfv
    @7
    vb
    wnf
    @5
    vb
    @6
    @3
    vb
    vg
    cG
    cX
    vb
    cG
    nfcv
    vb
    cX
    @10
    @12
    @11
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
    @17
    vb
    vz
    cT
    @16
    vb
    cT
    nfra1
    vb
    cT
    nfcv
    nfriota
    nfcxfr
    nfcsb
    nfeq1
    a1i
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
    cdlemkid4
    @3
    @6
    wceq
    @15
    @7
    wb
    @5
    @3
    @6
    @3
    eqeq1
    adantl
    @9
    cT
    wcel
    @14
    wa
    #
    @15
    wi
    @5
    @18
    @3
    eqidd
    a1i
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
    cdlemkid5
    @0
    @2
    @14
    vb
    cT
    wrex
    @4
    cB
    cR
    cT
    vb
    cH
    cK
    cW
    @1
    @13
    cdlemk5.b
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    cdlemftr2
    3ad2ant1
    riotasv3d
    mpan2
end
