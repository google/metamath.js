include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cdleme19e.mm"
include "oveq2d.mm"
include "3eqtr4g.mm"

theorem cdleme19f
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
  assume cdleme19.n: |- N = ( ( P .\/ Q ) ./\ ( F .\/ D ) )
  assume cdleme19.o: |- O = ( ( P .\/ Q ) ./\ ( G .\/ Y ) )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) /\ R e. A ) /\ ( ( P =/= Q /\ S =/= T ) /\ ( -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( P .\/ Q ) ) /\ ( R .<_ ( P .\/ Q ) /\ R .<_ ( S .\/ T ) ) ) ) -> N = O )

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
    cR
    cA
    wcel
    w3a
    cP
    cQ
    wne
    cS
    cT
    wne
    wa
    cS
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    wn
    cT
    @0
    c.le
    wbr
    wn
    wa
    cR
    @0
    c.le
    wbr
    cR
    cS
    cT
    c.or
    co
    c.le
    wbr
    wa
    w3a
    w3a
    #
    @0
    cF
    cD
    c.or
    co
    #
    c.an
    co
    @0
    cG
    cY
    c.or
    co
    #
    c.an
    co
    cN
    cO
    @1
    @2
    @3
    @0
    c.an
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
    cdleme19e
    oveq2d
    cdleme19.n
    cdleme19.o
    3eqtr4g
end
