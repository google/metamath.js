include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "cfv.mm"
include "simp23l.mm"
include "pm2.24d.mm"
include "clat.mm"
include "wb.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp21l.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latleeqm1.mm"
include "syl3anc.mm"
include "latmcl.mm"
include "simp21r.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp31.mm"
include "cdleme27cl.mm"
include "syl122anc.mm"
include "latjcl.mm"
include "simp33.mm"
include "wi.mm"
include "latmlem1.mm"
include "syl13anc.mm"
include "mpd.mm"
include "latlej2.mm"
include "lattrd.mm"
include "breq1.mm"
include "syl5ibcom.mm"
include "sylbid.mm"
include "wo.mm"
include "simp22.mm"
include "pm4.53.mm"
include "sylib.mm"
include "mpjaod.mm"
include "cdleme31fv2.mm"
include "syl2anc.mm"
include "simp1.mm"
include "simp23.mm"
include "simp32.mm"
include "cdleme32a.mm"
include "3brtr4d.mm"

theorem cdleme32e
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cU: class U
  let cE: class E
  let cF: class F
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cW: class W
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let cR: class R
  assume cdleme32.b: |- B = ( Base ` K )
  assume cdleme32.l: |- .<_ = ( le ` K )
  assume cdleme32.j: |- .\/ = ( join ` K )
  assume cdleme32.m: |- ./\ = ( meet ` K )
  assume cdleme32.a: |- A = ( Atoms ` K )
  assume cdleme32.h: |- H = ( LHyp ` K )
  assume cdleme32.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme32.c: |- C = ( ( s .\/ U ) ./\ ( Q .\/ ( ( P .\/ s ) ./\ W ) ) )
  assume cdleme32.d: |- D = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )
  assume cdleme32.e: |- E = ( ( P .\/ Q ) ./\ ( D .\/ ( ( s .\/ t ) ./\ W ) ) )
  assume cdleme32.i: |- I = ( iota_ y e. B A. t e. A ( ( -. t .<_ W /\ -. t .<_ ( P .\/ Q ) ) -> y = E ) )
  assume cdleme32.n: |- N = if ( s .<_ ( P .\/ Q ) , I , C )
  assume cdleme32.o: |- O = ( iota_ z e. B A. s e. A ( ( -. s .<_ W /\ ( s .\/ ( x ./\ W ) ) = x ) -> z = ( N .\/ ( x ./\ W ) ) ) )
  assume cdleme32.f: |- F = ( x e. B |-> if ( ( P =/= Q /\ -. x .<_ W ) , O , x ) )

  disjoint s t
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B s
  disjoint B t
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C y
  disjoint D s
  disjoint D y
  disjoint D z
  disjoint E y
  disjoint H s
  disjoint H t
  disjoint .\/ s
  disjoint .\/ t
  disjoint .\/ x
  disjoint .\/ y
  disjoint .\/ z
  disjoint K s
  disjoint K t
  disjoint .<_ s
  disjoint .<_ t
  disjoint .<_ x
  disjoint .<_ y
  disjoint .<_ z
  disjoint ./\ s
  disjoint ./\ t
  disjoint ./\ x
  disjoint ./\ y
  disjoint ./\ z
  disjoint N x
  disjoint N z
  disjoint P s
  disjoint P t
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint Q s
  disjoint Q t
  disjoint Q x
  disjoint Q y
  disjoint Q z
  disjoint U s
  disjoint U t
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint W s
  disjoint W t
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint X s
  disjoint X t
  disjoint X x
  disjoint X z
  disjoint H y
  disjoint K y
  disjoint Y y
  disjoint H z
  disjoint K z
  disjoint Y s
  disjoint Y t
  disjoint Y x
  disjoint Y z
  disjoint R s
  disjoint R t
  disjoint R y
  disjoint R x
  disjoint R z
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( X e. B /\ Y e. B ) /\ -. ( P =/= Q /\ -. X .<_ W ) /\ ( P =/= Q /\ -. Y .<_ W ) ) /\ ( ( s e. A /\ -. s .<_ W ) /\ ( s .\/ ( Y ./\ W ) ) = Y /\ X .<_ Y ) ) -> ( F ` X ) .<_ ( F ` Y ) )

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
    w3a
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    cP
    cQ
    wne
    #
    cX
    cW
    c.le
    wbr
    #
    wn
    wa
    wn
    #
    @9
    cY
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    vs
    cv
    #
    cA
    wcel
    @15
    cW
    c.le
    wbr
    wn
    wa
    #
    @15
    cY
    cW
    c.an
    co
    #
    c.or
    co
    cY
    wceq
    #
    cX
    cY
    c.le
    wbr
    #
    w3a
    #
    w3a
    #
    cX
    cN
    @17
    c.or
    co
    #
    cX
    cF
    cfv
    #
    cY
    cF
    cfv
    #
    c.le
    @21
    @9
    wn
    #
    cX
    @22
    c.le
    wbr
    #
    @10
    @21
    @9
    @26
    @9
    @12
    @8
    @11
    @5
    @20
    simp23l
    #
    pm2.24d
    @21
    @10
    cX
    cW
    c.an
    co
    #
    cX
    wceq
    #
    @26
    @21
    cK
    clat
    wcel
    #
    @6
    cW
    cB
    wcel
    #
    @10
    @29
    wb
    @21
    @0
    @30
    @0
    @1
    @3
    @4
    @14
    @20
    simp11l
    cK
    hllat
    syl
    #
    @6
    @7
    @11
    @13
    @5
    @20
    simp21l
    #
    @21
    @1
    @31
    @0
    @1
    @3
    @4
    @14
    @20
    simp11r
    cB
    cH
    cK
    cW
    cdleme32.b
    cdleme32.h
    lhpbase
    syl
    #
    cB
    cK
    c.le
    c.an
    cX
    cW
    cdleme32.b
    cdleme32.l
    cdleme32.m
    latleeqm1
    syl3anc
    @21
    @28
    @22
    c.le
    wbr
    @29
    @26
    @21
    cB
    cK
    c.le
    @28
    @17
    @22
    cdleme32.b
    cdleme32.l
    @32
    @21
    @30
    @6
    @31
    @28
    cB
    wcel
    @32
    @33
    @34
    cB
    cK
    c.an
    cX
    cW
    cdleme32.b
    cdleme32.m
    latmcl
    syl3anc
    @21
    @30
    @7
    @31
    @17
    cB
    wcel
    #
    @32
    @6
    @7
    @11
    @13
    @5
    @20
    simp21r
    #
    @34
    cB
    cK
    c.an
    cY
    cW
    cdleme32.b
    cdleme32.m
    latmcl
    syl3anc
    #
    @21
    @30
    cN
    cB
    wcel
    #
    @35
    @22
    cB
    wcel
    @32
    @21
    @2
    @3
    @4
    @16
    @9
    @38
    @2
    @3
    @4
    @14
    @20
    simp11
    @2
    @3
    @4
    @14
    @20
    simp12
    @2
    @3
    @4
    @14
    @20
    simp13
    @5
    @14
    @16
    @18
    @19
    simp31
    #
    @27
    vt
    vy
    cA
    cB
    cN
    cI
    cP
    cQ
    cU
    cC
    cH
    c.or
    cK
    c.le
    c.an
    cE
    cW
    cD
    vs
    cdleme32.b
    cdleme32.l
    cdleme32.j
    cdleme32.m
    cdleme32.a
    cdleme32.h
    cdleme32.u
    cdleme32.c
    cdleme32.d
    cdleme32.e
    cdleme32.i
    cdleme32.n
    cdleme27cl
    syl122anc
    #
    @37
    cB
    c.or
    cK
    cN
    @17
    cdleme32.b
    cdleme32.j
    latjcl
    syl3anc
    @21
    @19
    @28
    @17
    c.le
    wbr
    #
    @5
    @14
    @16
    @18
    @19
    simp33
    @21
    @30
    @6
    @7
    @31
    @19
    @41
    wi
    @32
    @33
    @36
    @34
    cB
    cK
    c.le
    c.an
    cX
    cY
    cW
    cdleme32.b
    cdleme32.l
    cdleme32.m
    latmlem1
    syl13anc
    mpd
    @21
    @30
    @38
    @35
    @17
    @22
    c.le
    wbr
    @32
    @40
    @37
    cB
    c.or
    cK
    c.le
    cN
    @17
    cdleme32.b
    cdleme32.l
    cdleme32.j
    latlej2
    syl3anc
    lattrd
    @28
    cX
    @22
    c.le
    breq1
    syl5ibcom
    sylbid
    @21
    @11
    @25
    @10
    wo
    @5
    @8
    @11
    @13
    @20
    simp22
    #
    @9
    @10
    pm4.53
    sylib
    mpjaod
    @21
    @6
    @11
    @23
    cX
    wceq
    @33
    @42
    vx
    cB
    cP
    cQ
    cF
    c.le
    cO
    cW
    cX
    cdleme32.f
    cdleme31fv2
    syl2anc
    @21
    @5
    @7
    @13
    @16
    @18
    @24
    @22
    wceq
    @5
    @14
    @20
    simp1
    @36
    @5
    @8
    @11
    @13
    @20
    simp23
    @39
    @5
    @14
    @16
    @18
    @19
    simp32
    vx
    vy
    vz
    vt
    cA
    cB
    cC
    cD
    cP
    cQ
    cU
    cE
    cF
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cN
    cO
    cW
    cY
    vs
    cdleme32.b
    cdleme32.l
    cdleme32.j
    cdleme32.m
    cdleme32.a
    cdleme32.h
    cdleme32.u
    cdleme32.c
    cdleme32.d
    cdleme32.e
    cdleme32.i
    cdleme32.n
    cdleme32.o
    cdleme32.f
    cdleme32a
    syl122anc
    3brtr4d
end
