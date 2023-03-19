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
include "simp3r.mm"
include "idltrn.mm"
include "3ad2ant1.mm"
include "eqeltrd.mm"
include "wsbc.mm"
include "csbeq2i.mm"
include "csbriota.mm"
include "a1i.mm"
include "syl5eq.mm"
include "sbcralg.mm"
include "sbcimg.mm"
include "sbc3an.mm"
include "sbcg.mm"
include "sbcne12.mm"
include "csbconstg.mm"
include "csbfv.mm"
include "neeq12d.mm"
include "syl5bb.mm"
include "3anbi123d.mm"
include "sbceq2g.mm"
include "imbi12d.mm"
include "bitrd.mm"
include "ralbidv.mm"
include "riotabidv.mm"
include "eqtrd.mm"
include "syl.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13l.mm"
include "simp13r.mm"
include "simp2.mm"
include "simp31.mm"
include "jca.mm"
include "cdlemkid2.mm"
include "syl113anc.mm"
include "3expa.mm"
include "eqeq2d.mm"
include "pm5.74da.mm"
include "ralbidva.mm"

theorem cdlemkid3N
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ N e. T /\ ( R ` F ) = ( R ` N ) ) /\ ( ( P e. A /\ -. P .<_ W ) /\ G = ( _I |` B ) ) ) -> [_ G / g ]_ X = ( iota_ z e. T A. b e. T ( ( b =/= ( _I |` B ) /\ ( R ` b ) =/= ( R ` F ) /\ ( R ` b ) =/= ( R ` G ) ) -> ( z ` P ) = P ) ) )

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
    #
    cG
    cid
    cB
    cres
    #
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
    vb
    cv
    #
    @4
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
    #
    w3a
    #
    cP
    vz
    cv
    cfv
    #
    vg
    cG
    cY
    csb
    #
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
    @15
    @16
    cP
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
    @7
    cG
    cT
    wcel
    #
    @8
    @21
    wceq
    @7
    cG
    @4
    cT
    @0
    @2
    @3
    @5
    simp3r
    @0
    @2
    @4
    cT
    wcel
    @6
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
    eqeltrd
    @25
    @8
    @10
    @12
    @11
    vg
    cv
    cR
    cfv
    #
    wne
    #
    w3a
    #
    @16
    cY
    wceq
    #
    wi
    #
    vb
    cT
    wral
    #
    vg
    cG
    wsbc
    #
    vz
    cT
    crio
    #
    @21
    @25
    @8
    vg
    cG
    @31
    vz
    cT
    crio
    #
    csb
    #
    @33
    vg
    cG
    cX
    @34
    cdlemk5.x
    csbeq2i
    @35
    @33
    wceq
    @25
    @31
    vg
    vz
    cG
    cT
    csbriota
    a1i
    syl5eq
    @25
    @32
    @20
    vz
    cT
    @25
    @32
    @30
    vg
    cG
    wsbc
    #
    vb
    cT
    wral
    @20
    @30
    vg
    vb
    cG
    cT
    cT
    sbcralg
    @25
    @36
    @19
    vb
    cT
    @25
    @36
    @28
    vg
    cG
    wsbc
    #
    @29
    vg
    cG
    wsbc
    #
    wi
    @19
    @28
    @29
    vg
    cG
    cT
    sbcimg
    @25
    @37
    @15
    @38
    @18
    @37
    @10
    vg
    cG
    wsbc
    #
    @12
    vg
    cG
    wsbc
    #
    @27
    vg
    cG
    wsbc
    #
    w3a
    @25
    @15
    @10
    @12
    @27
    vg
    cG
    sbc3an
    @25
    @39
    @10
    @40
    @12
    @41
    @14
    @10
    vg
    cG
    cT
    sbcg
    @12
    vg
    cG
    cT
    sbcg
    @41
    vg
    cG
    @11
    csb
    #
    vg
    cG
    @26
    csb
    #
    wne
    @25
    @14
    vg
    cG
    @11
    @26
    sbcne12
    @25
    @42
    @11
    @43
    @13
    vg
    cG
    @11
    cT
    csbconstg
    @43
    @13
    wceq
    @25
    vg
    cG
    cR
    csbfv
    a1i
    neeq12d
    syl5bb
    3anbi123d
    syl5bb
    vg
    cG
    @16
    cY
    cT
    sbceq2g
    imbi12d
    bitrd
    ralbidv
    bitrd
    riotabidv
    eqtrd
    syl
    @7
    @20
    @24
    vz
    cT
    @7
    @19
    @23
    vb
    cT
    @7
    @9
    cT
    wcel
    #
    wa
    #
    @15
    @18
    @22
    @45
    @15
    wa
    @17
    cP
    @16
    @7
    @44
    @15
    @17
    cP
    wceq
    #
    @7
    @44
    @15
    w3a
    #
    @0
    @2
    @3
    @5
    @44
    @10
    wa
    @46
    @0
    @2
    @6
    @44
    @15
    simp11
    @0
    @2
    @6
    @44
    @15
    simp12
    @3
    @5
    @0
    @2
    @44
    @15
    simp13l
    @3
    @5
    @0
    @2
    @44
    @15
    simp13r
    @47
    @44
    @10
    @7
    @44
    @15
    simp2
    @7
    @44
    @10
    @12
    @14
    simp31
    jca
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
    cdlemkid2
    syl113anc
    3expa
    eqeq2d
    pm5.74da
    ralbidva
    riotabidv
    eqtrd
end
