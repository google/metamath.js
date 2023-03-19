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
include "csb.mm"
include "simpl1.mm"
include "simp21l.mm"
include "simp23.mm"
include "simp3r.mm"
include "3jca.mm"
include "adantr.mm"
include "simpl3l.mm"
include "simpr.mm"
include "cdlemkid.mm"
include "syl112anc.mm"
include "simpl1l.mm"
include "simpl1r.mm"
include "idltrn.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "simpl21.mm"
include "simpl22.mm"
include "jca.mm"
include "simpl23.mm"
include "simpl3.mm"
include "cdlemk35s.mm"
include "syl131anc.mm"
include "pm2.61dane.mm"

theorem cdlemk35s-id
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( F e. T /\ F =/= ( _I |` B ) ) /\ G e. T /\ N e. T ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) ) -> [_ G / g ]_ X e. T )

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
    cN
    cT
    wcel
    #
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
    cF
    cR
    cfv
    cN
    cR
    cfv
    wceq
    #
    wa
    #
    w3a
    #
    vg
    cG
    cX
    csb
    #
    cT
    wcel
    #
    cG
    @4
    @13
    cG
    @4
    wceq
    #
    wa
    #
    @14
    @4
    cT
    @17
    @2
    @3
    @8
    @11
    w3a
    #
    @10
    @16
    @14
    @4
    wceq
    @2
    @9
    @12
    @16
    simpl1
    @13
    @18
    @16
    @13
    @3
    @8
    @11
    @3
    @5
    @7
    @8
    @2
    @12
    simp21l
    @2
    @6
    @7
    @8
    @12
    simp23
    @2
    @9
    @10
    @11
    simp3r
    3jca
    adantr
    @10
    @11
    @2
    @9
    @16
    simpl3l
    @13
    @16
    simpr
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
    cdlemkid
    syl112anc
    @17
    @0
    @1
    @4
    cT
    wcel
    @0
    @1
    @9
    @12
    @16
    simpl1l
    @0
    @1
    @9
    @12
    @16
    simpl1r
    cB
    cT
    cH
    cK
    cW
    cdlemk5.b
    cdlemk5.h
    cdlemk5.t
    idltrn
    syl2anc
    eqeltrd
    @13
    cG
    @4
    wne
    #
    wa
    #
    @2
    @6
    @7
    @19
    wa
    @8
    @12
    @15
    @2
    @9
    @12
    @19
    simpl1
    @6
    @7
    @8
    @2
    @12
    @19
    simpl21
    @20
    @7
    @19
    @6
    @7
    @8
    @2
    @12
    @19
    simpl22
    @13
    @19
    simpr
    jca
    @6
    @7
    @8
    @2
    @12
    @19
    simpl23
    @2
    @9
    @12
    @19
    simpl3
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
    cdlemk35s
    syl131anc
    pm2.61dane
end
