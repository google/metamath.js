include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "wss.mm"
include "cid.mm"
include "cres.mm"
include "cop.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cdlemn11c.mm"
include "wi.mm"
include "wb.mm"
include "simp1.mm"
include "simp21.mm"
include "dicelval3.mm"
include "syl2anc.mm"
include "simp23.mm"
include "dibelval3.mm"
include "anbi12d.mm"
include "reeanv.mm"
include "simpl1.mm"
include "simpl21.mm"
include "simpl22.mm"
include "simpl23.mm"
include "simpr1r.mm"
include "simpr1l.mm"
include "simpr3.mm"
include "cdlemn9.mm"
include "syl123anc.mm"
include "simpr2.mm"
include "cdlemn10.mm"
include "syl133anc.mm"
include "3exp2.mm"
include "oveq12.mm"
include "eqeq2d.mm"
include "imbi1d.mm"
include "imbi2d.mm"
include "biimprd.mm"
include "com23.mm"
include "impr.mm"
include "com12.mm"
include "syl6.mm"
include "rexlimdvv.mm"
include "syl5bir.mm"
include "sylbid.mm"
include "mpd.mm"

theorem cdlemn11pre
  let cA: class A
  let cB: class B
  let cP: class P
  let c.pl: class .+
  let c.po: class .(+)
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cU: class U
  let vh: setvar h
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cN: class N
  let cO: class O
  let cW: class W
  let cX: class X
  let vg: setvar g
  let vs: setvar s
  let vy: setvar y
  let vz: setvar z
  assume cdlemn11a.b: |- B = ( Base ` K )
  assume cdlemn11a.l: |- .<_ = ( le ` K )
  assume cdlemn11a.j: |- .\/ = ( join ` K )
  assume cdlemn11a.a: |- A = ( Atoms ` K )
  assume cdlemn11a.h: |- H = ( LHyp ` K )
  assume cdlemn11a.p: |- P = ( ( oc ` K ) ` W )
  assume cdlemn11a.o: |- O = ( h e. T |-> ( _I |` B ) )
  assume cdlemn11a.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemn11a.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemn11a.e: |- E = ( ( TEndo ` K ) ` W )
  assume cdlemn11a.i: |- I = ( ( DIsoB ` K ) ` W )
  assume cdlemn11a.J: |- J = ( ( DIsoC ` K ) ` W )
  assume cdlemn11a.u: |- U = ( ( DVecH ` K ) ` W )
  assume cdlemn11a.d: |- .+ = ( +g ` U )
  assume cdlemn11a.s: |- .(+) = ( LSSum ` U )
  assume cdlemn11a.f: |- F = ( iota_ h e. T ( h ` P ) = Q )
  assume cdlemn11a.g: |- G = ( iota_ h e. T ( h ` P ) = N )

  disjoint .<_ h
  disjoint A h
  disjoint B h
  disjoint H h
  disjoint K h
  disjoint N h
  disjoint P h
  disjoint Q h
  disjoint T h
  disjoint W h
  disjoint g s
  disjoint g y
  disjoint g z
  disjoint .+ g
  disjoint s y
  disjoint s z
  disjoint .+ s
  disjoint y z
  disjoint .+ y
  disjoint .+ z
  disjoint .\/ g
  disjoint .\/ s
  disjoint .\/ y
  disjoint .\/ z
  disjoint g h
  disjoint .<_ g
  disjoint h s
  disjoint h y
  disjoint h z
  disjoint .<_ s
  disjoint .<_ y
  disjoint .<_ z
  disjoint A g
  disjoint A s
  disjoint A y
  disjoint A z
  disjoint B g
  disjoint B s
  disjoint B y
  disjoint B z
  disjoint E g
  disjoint E s
  disjoint F g
  disjoint G g
  disjoint G s
  disjoint G y
  disjoint G z
  disjoint I g
  disjoint I s
  disjoint I y
  disjoint I z
  disjoint .(+) g
  disjoint .(+) s
  disjoint .(+) y
  disjoint .(+) z
  disjoint H g
  disjoint H s
  disjoint H y
  disjoint H z
  disjoint K g
  disjoint K s
  disjoint K y
  disjoint K z
  disjoint N g
  disjoint N s
  disjoint N y
  disjoint N z
  disjoint J g
  disjoint J s
  disjoint J y
  disjoint J z
  disjoint Q g
  disjoint Q s
  disjoint Q y
  disjoint Q z
  disjoint R s
  disjoint T g
  disjoint T s
  disjoint T y
  disjoint T z
  disjoint O g
  disjoint O s
  disjoint U y
  disjoint U z
  disjoint W g
  disjoint W s
  disjoint W y
  disjoint W z
  disjoint X g
  disjoint X s
  disjoint X y
  disjoint X z
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( Q e. A /\ -. Q .<_ W ) /\ ( N e. A /\ -. N .<_ W ) /\ ( X e. B /\ X .<_ W ) ) /\ ( J ` N ) C_ ( ( J ` Q ) .(+) ( I ` X ) ) ) -> N .<_ ( Q .\/ X ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    #
    cN
    cA
    wcel
    cN
    cW
    c.le
    wbr
    wn
    wa
    #
    cX
    cB
    wcel
    cX
    cW
    c.le
    wbr
    wa
    #
    w3a
    #
    cN
    cJ
    cfv
    cQ
    cJ
    cfv
    #
    cX
    cI
    cfv
    #
    c.po
    co
    wss
    #
    w3a
    #
    cG
    cid
    cT
    cres
    cop
    #
    vy
    cv
    #
    vz
    cv
    #
    c.pl
    co
    #
    wceq
    #
    vz
    @6
    wrex
    vy
    @5
    wrex
    cN
    cQ
    cX
    c.or
    co
    c.le
    wbr
    #
    vy
    vz
    cA
    cB
    cP
    c.pl
    c.po
    cQ
    cR
    cT
    cU
    vh
    cE
    cF
    cG
    cH
    cI
    cJ
    c.or
    cK
    c.le
    cN
    cO
    cW
    cX
    cdlemn11a.b
    cdlemn11a.l
    cdlemn11a.j
    cdlemn11a.a
    cdlemn11a.h
    cdlemn11a.p
    cdlemn11a.o
    cdlemn11a.t
    cdlemn11a.r
    cdlemn11a.e
    cdlemn11a.i
    cdlemn11a.J
    cdlemn11a.u
    cdlemn11a.d
    cdlemn11a.s
    cdlemn11a.f
    cdlemn11a.g
    cdlemn11c
    @8
    @13
    @14
    vy
    vz
    @5
    @6
    @8
    @10
    @5
    wcel
    #
    @11
    @6
    wcel
    #
    wa
    @10
    cF
    vs
    cv
    #
    cfv
    @17
    cop
    #
    wceq
    #
    vs
    cE
    wrex
    #
    @11
    vg
    cv
    #
    cO
    cop
    #
    wceq
    #
    @21
    cR
    cfv
    cX
    c.le
    wbr
    #
    wa
    #
    vg
    cT
    wrex
    #
    wa
    #
    @13
    @14
    wi
    #
    @8
    @15
    @20
    @16
    @26
    @8
    @0
    @1
    @15
    @20
    wb
    @0
    @4
    @7
    simp1
    #
    @0
    @1
    @2
    @3
    @7
    simp21
    cA
    cP
    cQ
    cT
    vh
    cE
    cF
    cH
    cJ
    cK
    c.le
    chlt
    cW
    @10
    vs
    cdlemn11a.l
    cdlemn11a.a
    cdlemn11a.h
    cdlemn11a.p
    cdlemn11a.t
    cdlemn11a.e
    cdlemn11a.J
    cdlemn11a.f
    dicelval3
    syl2anc
    @8
    @0
    @3
    @16
    @26
    wb
    @29
    @0
    @1
    @2
    @3
    @7
    simp23
    cB
    cR
    cT
    vg
    vh
    cH
    cI
    cK
    c.le
    chlt
    cW
    cX
    @11
    cO
    cdlemn11a.b
    cdlemn11a.l
    cdlemn11a.h
    cdlemn11a.t
    cdlemn11a.r
    cdlemn11a.o
    cdlemn11a.i
    dibelval3
    syl2anc
    anbi12d
    @27
    @19
    @25
    wa
    #
    vg
    cT
    wrex
    vs
    cE
    wrex
    @8
    @28
    @19
    @25
    vs
    vg
    cE
    cT
    reeanv
    @8
    @30
    @28
    vs
    vg
    cE
    cT
    @8
    @17
    cE
    wcel
    #
    @21
    cT
    wcel
    #
    wa
    #
    @24
    @9
    @18
    @22
    c.pl
    co
    #
    wceq
    #
    @14
    wi
    #
    wi
    #
    @30
    @28
    wi
    @8
    @33
    @24
    @35
    @14
    @8
    @33
    @24
    @35
    w3a
    #
    wa
    #
    @0
    @1
    @2
    @3
    @32
    cQ
    @21
    cfv
    cN
    wceq
    #
    @24
    @14
    @0
    @4
    @7
    @38
    simpl1
    #
    @1
    @2
    @3
    @0
    @7
    @38
    simpl21
    #
    @1
    @2
    @3
    @0
    @7
    @38
    simpl22
    #
    @1
    @2
    @3
    @0
    @7
    @38
    simpl23
    @31
    @32
    @24
    @35
    @8
    simpr1r
    #
    @39
    @0
    @1
    @2
    @31
    @32
    @35
    @40
    @41
    @42
    @43
    @31
    @32
    @24
    @35
    @8
    simpr1l
    @44
    @8
    @33
    @24
    @35
    simpr3
    cA
    cB
    cP
    c.pl
    cQ
    cN
    cT
    cU
    vg
    vh
    cE
    cF
    cG
    cH
    cK
    c.le
    cO
    cW
    vs
    cdlemn11a.b
    cdlemn11a.l
    cdlemn11a.a
    cdlemn11a.h
    cdlemn11a.p
    cdlemn11a.o
    cdlemn11a.t
    cdlemn11a.e
    cdlemn11a.u
    cdlemn11a.d
    cdlemn11a.f
    cdlemn11a.g
    cdlemn9
    syl123anc
    @8
    @33
    @24
    @35
    simpr2
    cA
    cB
    cQ
    cR
    cN
    cT
    vg
    cH
    c.or
    cK
    c.le
    cW
    cX
    cdlemn11a.b
    cdlemn11a.l
    cdlemn11a.j
    cdlemn11a.a
    cdlemn11a.h
    cdlemn11a.t
    cdlemn11a.r
    cdlemn10
    syl133anc
    3exp2
    @30
    @37
    @28
    @19
    @23
    @24
    @37
    @28
    wi
    @19
    @23
    wa
    #
    @37
    @24
    @28
    @45
    @24
    @28
    wi
    @37
    @45
    @28
    @36
    @24
    @45
    @13
    @35
    @14
    @45
    @12
    @34
    @9
    @10
    @18
    @11
    @22
    c.pl
    oveq12
    eqeq2d
    imbi1d
    imbi2d
    biimprd
    com23
    impr
    com12
    syl6
    rexlimdvv
    syl5bir
    sylbid
    rexlimdvv
    mpd
end
