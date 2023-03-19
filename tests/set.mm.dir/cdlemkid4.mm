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
include "eqtri.mm"
include "a1i.mm"
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
include "wb.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3l.mm"
include "simpl3r.mm"
include "simprlr.mm"
include "simprr1.mm"
include "jca.mm"
include "cdlemkid2.mm"
include "syl113anc.mm"
include "eqeq2d.mm"
include "simprll.mm"
include "ltrnideq.mm"
include "syl3anc.mm"
include "bitr4d.mm"
include "exp44.mm"
include "imp41.mm"
include "pm5.74da.mm"
include "ralbidva.mm"
include "riotabidva.mm"

theorem cdlemkid4
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ N e. T /\ ( R ` F ) = ( R ` N ) ) /\ ( ( P e. A /\ -. P .<_ W ) /\ G = ( _I |` B ) ) ) -> [_ G / g ]_ X = ( iota_ z e. T A. b e. T ( ( b =/= ( _I |` B ) /\ ( R ` b ) =/= ( R ` F ) /\ ( R ` b ) =/= ( R ` G ) ) -> z = ( _I |` B ) ) ) )

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
    #
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
    @4
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
    @22
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
    @26
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
    @17
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
    @22
    @8
    @34
    wceq
    @26
    @8
    vg
    cG
    @32
    vz
    cT
    crio
    #
    csb
    @34
    vg
    cG
    cX
    @35
    cdlemk5.x
    csbeq2i
    @32
    vg
    vz
    cG
    cT
    csbriota
    eqtri
    a1i
    @26
    @33
    @21
    vz
    cT
    @26
    @33
    @31
    vg
    cG
    wsbc
    #
    vb
    cT
    wral
    @21
    @31
    vg
    vb
    cG
    cT
    cT
    sbcralg
    @26
    @36
    @20
    vb
    cT
    @26
    @36
    @29
    vg
    cG
    wsbc
    #
    @30
    vg
    cG
    wsbc
    #
    wi
    @20
    @29
    @30
    vg
    cG
    cT
    sbcimg
    @26
    @37
    @15
    @38
    @19
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
    @28
    vg
    cG
    wsbc
    #
    w3a
    @26
    @15
    @10
    @12
    @28
    vg
    cG
    sbc3an
    @26
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
    @27
    csb
    #
    wne
    @26
    @14
    vg
    cG
    @11
    @27
    sbcne12
    @26
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
    @26
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
    @17
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
    @21
    @25
    vz
    cT
    @7
    @16
    cT
    wcel
    #
    wa
    #
    @20
    @24
    vb
    cT
    @45
    @9
    cT
    wcel
    #
    wa
    @15
    @19
    @23
    @7
    @44
    @46
    @15
    @19
    @23
    wb
    #
    @7
    @44
    @46
    @15
    @47
    @7
    @44
    @46
    wa
    #
    @15
    wa
    #
    wa
    #
    @19
    @17
    cP
    wceq
    #
    @23
    @50
    @18
    cP
    @17
    @50
    @0
    @2
    @3
    @5
    @46
    @10
    wa
    @18
    cP
    wceq
    @0
    @2
    @6
    @49
    simpl1
    #
    @0
    @2
    @6
    @49
    simpl2
    @3
    @5
    @0
    @2
    @49
    simpl3l
    #
    @3
    @5
    @0
    @2
    @49
    simpl3r
    @50
    @46
    @10
    @7
    @44
    @46
    @15
    simprlr
    @10
    @12
    @14
    @48
    @7
    simprr1
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
    eqeq2d
    @50
    @0
    @44
    @3
    @23
    @51
    wb
    @52
    @7
    @44
    @46
    @15
    simprll
    @53
    cA
    cB
    cP
    cT
    @16
    cH
    cK
    c.le
    cW
    cdlemk5.b
    cdlemk5.l
    cdlemk5.a
    cdlemk5.h
    cdlemk5.t
    ltrnideq
    syl3anc
    bitr4d
    exp44
    imp41
    pm5.74da
    ralbidva
    riotabidva
    eqtrd
end
