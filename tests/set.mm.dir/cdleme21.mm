include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3l.mm"
include "simpl3r.mm"
include "simpr.mm"
include "cdleme21j.mm"
include "syl113anc.mm"
include "simp3ll.mm"
include "adantr.mm"
include "simp3r3.mm"
include "simp3r1.mm"
include "simp3r2.mm"
include "3jca.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "cdleme18d.mm"
include "pm2.61dan.mm"

theorem cdleme21
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
  let cW: class W
  let cY: class Y
  let vr: setvar r
  let vz: setvar z
  assume cdleme21.l: |- .<_ = ( le ` K )
  assume cdleme21.j: |- .\/ = ( join ` K )
  assume cdleme21.m: |- ./\ = ( meet ` K )
  assume cdleme21.a: |- A = ( Atoms ` K )
  assume cdleme21.h: |- H = ( LHyp ` K )
  assume cdleme21.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme21.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme21g.g: |- G = ( ( T .\/ U ) ./\ ( Q .\/ ( ( P .\/ T ) ./\ W ) ) )
  assume cdleme21g.d: |- D = ( ( R .\/ S ) ./\ W )
  assume cdleme21g.y: |- Y = ( ( R .\/ T ) ./\ W )
  assume cdleme21g.n: |- N = ( ( P .\/ Q ) ./\ ( F .\/ D ) )
  assume cdleme21g.o: |- O = ( ( P .\/ Q ) ./\ ( G .\/ Y ) )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) ) /\ ( ( P =/= Q /\ S =/= T ) /\ ( -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( P .\/ Q ) /\ R .<_ ( P .\/ Q ) ) ) ) -> N = O )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    w3a
    #
    cR
    cA
    wcel
    cR
    cW
    c.le
    wbr
    wn
    wa
    cS
    cA
    wcel
    cS
    cW
    c.le
    wbr
    wn
    wa
    cT
    cA
    wcel
    cT
    cW
    c.le
    wbr
    wn
    wa
    w3a
    #
    cP
    cQ
    wne
    #
    cS
    cT
    wne
    #
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
    @5
    c.le
    wbr
    wn
    #
    cR
    @5
    c.le
    wbr
    #
    w3a
    #
    wa
    #
    w3a
    #
    vr
    cv
    #
    cW
    c.le
    wbr
    wn
    cP
    @12
    c.or
    co
    cQ
    @12
    c.or
    co
    wceq
    wa
    vr
    cA
    wrex
    #
    cN
    cO
    wceq
    #
    @11
    @13
    wa
    @0
    @1
    @4
    @9
    @13
    @14
    @0
    @1
    @10
    @13
    simpl1
    @0
    @1
    @10
    @13
    simpl2
    @4
    @9
    @0
    @1
    @13
    simpl3l
    @4
    @9
    @0
    @1
    @13
    simpl3r
    @11
    @13
    simpr
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
    vr
    cdleme21.l
    cdleme21.j
    cdleme21.m
    cdleme21.a
    cdleme21.h
    cdleme21.u
    cdleme21.f
    cdleme21g.g
    cdleme21g.d
    cdleme21g.y
    cdleme21g.n
    cdleme21g.o
    cdleme21j
    syl113anc
    @11
    @13
    wn
    #
    wa
    @0
    @1
    @2
    @8
    @6
    @7
    w3a
    #
    @15
    @14
    @0
    @1
    @10
    @15
    simpl1
    @0
    @1
    @10
    @15
    simpl2
    @11
    @2
    @15
    @2
    @3
    @9
    @0
    @1
    simp3ll
    adantr
    @11
    @16
    @15
    @11
    @8
    @6
    @7
    @6
    @7
    @8
    @4
    @0
    @1
    simp3r3
    @6
    @7
    @8
    @4
    @0
    @1
    simp3r1
    @6
    @7
    @8
    @4
    @0
    @1
    simp3r2
    3jca
    adantr
    @11
    @15
    simpr
    cA
    cG
    cP
    cQ
    cR
    cS
    cT
    cU
    cO
    cF
    cN
    cH
    c.or
    cK
    c.le
    c.an
    cW
    vr
    cdleme21.l
    cdleme21.j
    cdleme21.m
    cdleme21.a
    cdleme21.h
    cdleme21.u
    cdleme21.f
    cN
    @5
    cF
    cD
    c.or
    co
    #
    c.an
    co
    @5
    cF
    cR
    cS
    c.or
    co
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    cdleme21g.n
    @17
    @19
    @5
    c.an
    cD
    @18
    cF
    c.or
    cdleme21g.d
    oveq2i
    oveq2i
    eqtri
    cdleme21g.g
    cO
    @5
    cG
    cY
    c.or
    co
    #
    c.an
    co
    @5
    cG
    cR
    cT
    c.or
    co
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    cdleme21g.o
    @20
    @22
    @5
    c.an
    cY
    @21
    cG
    c.or
    cdleme21g.y
    oveq2i
    oveq2i
    eqtri
    cdleme18d
    syl113anc
    pm2.61dan
end
