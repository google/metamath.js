include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl22.mm"
include "simpl23.mm"
include "simp21l.mm"
include "adantr.mm"
include "simpl31.mm"
include "simp321.mm"
include "simp322.mm"
include "jca.mm"
include "simp323.mm"
include "anim1i.mm"
include "cdleme19f.mm"
include "syl133anc.mm"
include "simpl11.mm"
include "simpl12.mm"
include "simpl13.mm"
include "simpl21.mm"
include "simpl32.mm"
include "simpr.mm"
include "simpl33.mm"
include "cdleme20m.mm"
include "syl333anc.mm"
include "pm2.61dan.mm"

theorem cdleme20
  let cA: class A
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cV: class V
  let cW: class W
  let cY: class Y
  assume cdleme19.l: |- .<_ = ( le ` K )
  assume cdleme19.j: |- .\/ = ( join ` K )
  assume cdleme19.m: |- ./\ = ( meet ` K )
  assume cdleme19.a: |- A = ( Atoms ` K )
  assume cdleme19.h: |- H = ( LHyp ` K )
  assume cdleme19.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme19.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme19.g: |- G = ( ( T .\/ U ) ./\ ( Q .\/ ( ( P .\/ T ) ./\ W ) ) )
  assume cdleme19.d: |- D = ( ( R .\/ S ) ./\ W )
  assume cdleme19.y: |- Y = ( ( R .\/ T ) ./\ W )
  assume cdleme20.v: |- V = ( ( S .\/ T ) ./\ W )
  assume cdleme20.n: |- N = ( ( P .\/ Q ) ./\ ( F .\/ D ) )
  assume cdleme20.o: |- O = ( ( P .\/ Q ) ./\ ( G .\/ Y ) )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) ) /\ ( ( P =/= Q /\ S =/= T ) /\ ( -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( P .\/ Q ) /\ R .<_ ( P .\/ Q ) ) /\ -. U .<_ ( S .\/ T ) ) ) -> N = O )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
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
    cR
    cA
    wcel
    #
    cR
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cS
    cA
    wcel
    cS
    cW
    c.le
    wbr
    wn
    wa
    #
    cT
    cA
    wcel
    cT
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    cP
    cQ
    wne
    cS
    cT
    wne
    wa
    #
    cS
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    cT
    @11
    c.le
    wbr
    wn
    #
    cR
    @11
    c.le
    wbr
    #
    w3a
    #
    cU
    cS
    cT
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    w3a
    #
    w3a
    #
    cR
    @16
    c.le
    wbr
    #
    cN
    cO
    wceq
    #
    @19
    @20
    wa
    #
    @3
    @7
    @8
    @4
    @10
    @12
    @13
    wa
    @14
    @20
    wa
    @21
    @3
    @9
    @18
    @20
    simpl1
    @6
    @7
    @8
    @3
    @18
    @20
    simpl22
    @6
    @7
    @8
    @3
    @18
    @20
    simpl23
    @19
    @4
    @20
    @4
    @5
    @7
    @8
    @3
    @18
    simp21l
    adantr
    @10
    @15
    @17
    @3
    @9
    @20
    simpl31
    @22
    @12
    @13
    @19
    @12
    @20
    @12
    @13
    @14
    @10
    @17
    @3
    @9
    simp321
    adantr
    @19
    @13
    @20
    @12
    @13
    @14
    @10
    @17
    @3
    @9
    simp322
    adantr
    jca
    @19
    @14
    @20
    @12
    @13
    @14
    @10
    @17
    @3
    @9
    simp323
    anim1i
    cA
    cD
    cP
    cQ
    cR
    cS
    cT
    cU
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cO
    cW
    cY
    cdleme19.l
    cdleme19.j
    cdleme19.m
    cdleme19.a
    cdleme19.h
    cdleme19.u
    cdleme19.f
    cdleme19.g
    cdleme19.d
    cdleme19.y
    cdleme20.n
    cdleme20.o
    cdleme19f
    syl133anc
    @19
    @20
    wn
    #
    wa
    #
    @0
    @1
    @2
    @6
    @7
    @8
    @10
    @15
    @23
    @17
    wa
    @21
    @0
    @1
    @2
    @9
    @18
    @23
    simpl11
    @0
    @1
    @2
    @9
    @18
    @23
    simpl12
    @0
    @1
    @2
    @9
    @18
    @23
    simpl13
    @6
    @7
    @8
    @3
    @18
    @23
    simpl21
    @6
    @7
    @8
    @3
    @18
    @23
    simpl22
    @6
    @7
    @8
    @3
    @18
    @23
    simpl23
    @10
    @15
    @17
    @3
    @9
    @23
    simpl31
    @10
    @15
    @17
    @3
    @9
    @23
    simpl32
    @24
    @23
    @17
    @19
    @23
    simpr
    @10
    @15
    @17
    @3
    @9
    @23
    simpl33
    jca
    cA
    cD
    cP
    cQ
    cR
    cS
    cT
    cU
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cO
    cV
    cW
    cY
    cdleme19.l
    cdleme19.j
    cdleme19.m
    cdleme19.a
    cdleme19.h
    cdleme19.u
    cdleme19.f
    cdleme19.g
    cdleme19.d
    cdleme19.y
    cdleme20.v
    cdleme20.n
    cdleme20.o
    cdleme20m
    syl333anc
    pm2.61dan
end
