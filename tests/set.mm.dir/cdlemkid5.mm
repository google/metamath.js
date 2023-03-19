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
include "csb.mm"
include "cv.mm"
include "wne.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "cdlemkid4.mm"
include "wreu.mm"
include "wrex.mm"
include "idltrn.mm"
include "3ad2ant1.mm"
include "eqidd.mm"
include "rgenw.mm"
include "eqeq1.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "sylancl.mm"
include "wb.mm"
include "cdlemftr2.mm"
include "reusv1.mm"
include "syl.mm"
include "mpbird.mm"
include "riotacl.mm"
include "eqeltrd.mm"

theorem cdlemkid5
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ N e. T /\ ( R ` F ) = ( R ` N ) ) /\ ( ( P e. A /\ -. P .<_ W ) /\ G = ( _I |` B ) ) ) -> [_ G / g ]_ X e. T )

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
    vg
    cG
    cX
    csb
    vb
    cv
    #
    @3
    wne
    @6
    cR
    cfv
    #
    @1
    wne
    @7
    cG
    cR
    cfv
    #
    wne
    w3a
    #
    vz
    cv
    #
    @3
    wceq
    #
    wi
    #
    vb
    cT
    wral
    #
    vz
    cT
    crio
    #
    cT
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
    @5
    @13
    vz
    cT
    wreu
    #
    @14
    cT
    wcel
    @5
    @15
    @13
    vz
    cT
    wrex
    #
    @5
    @3
    cT
    wcel
    #
    @9
    @3
    @3
    wceq
    #
    wi
    #
    vb
    cT
    wral
    #
    @16
    @0
    @2
    @17
    @4
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
    @19
    vb
    cT
    @9
    @3
    eqidd
    rgenw
    @13
    @20
    vz
    @3
    cT
    @11
    @12
    @19
    vb
    cT
    @11
    @11
    @18
    @9
    @10
    @3
    @3
    eqeq1
    imbi2d
    ralbidv
    rspcev
    sylancl
    @5
    @9
    vb
    cT
    wrex
    #
    @15
    @16
    wb
    @0
    @2
    @21
    @4
    cB
    cR
    cT
    vb
    cH
    cK
    cW
    @1
    @8
    cdlemk5.b
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    cdlemftr2
    3ad2ant1
    @9
    vz
    vb
    cT
    cT
    @3
    reusv1
    syl
    mpbird
    @13
    vz
    cT
    riotacl
    syl
    eqeltrd
end
