include "cv.mm"
include "co.mm"
include "eqid.mm"
include "cdleme21f.mm"

theorem cdleme21g
  let vz: setvar z
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) /\ ( P =/= Q /\ -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( P .\/ Q ) ) ) /\ ( ( R e. A /\ -. R .<_ W ) /\ ( R .<_ ( P .\/ Q ) /\ U .<_ ( S .\/ T ) ) /\ ( ( z e. A /\ -. z .<_ W ) /\ ( P .\/ z ) = ( S .\/ z ) ) ) ) -> N = O )

  proof
    vz
    cA
    vz
    cv
    #
    cU
    c.or
    co
    cQ
    cP
    @0
    c.or
    co
    cW
    c.an
    co
    c.or
    co
    c.an
    co
    #
    cD
    cP
    cQ
    cR
    cS
    cT
    cU
    cR
    @0
    c.or
    co
    cW
    c.an
    co
    #
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
    cP
    cQ
    c.or
    co
    @1
    @2
    c.or
    co
    c.an
    co
    #
    cdleme21.l
    cdleme21.j
    cdleme21.m
    cdleme21.a
    cdleme21.h
    cdleme21.u
    cdleme21.f
    @1
    eqid
    cdleme21g.d
    @2
    eqid
    cdleme21g.n
    @3
    eqid
    cdleme21g.g
    cdleme21g.y
    cdleme21g.o
    cdleme21f
end
