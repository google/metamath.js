include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "hlatjcom.mm"
include "wceq.mm"
include "oveq2i.mm"
include "a1i.mm"
include "oveq12d.mm"
include "syl6reqr.mm"

theorem cdleme43aN
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let cE: class E
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume cdleme43.b: |- B = ( Base ` K )
  assume cdleme43.l: |- .<_ = ( le ` K )
  assume cdleme43.j: |- .\/ = ( join ` K )
  assume cdleme43.m: |- ./\ = ( meet ` K )
  assume cdleme43.a: |- A = ( Atoms ` K )
  assume cdleme43.h: |- H = ( LHyp ` K )
  assume cdleme43.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme43.x: |- X = ( ( Q .\/ P ) ./\ W )
  assume cdleme43.c: |- C = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme43.f: |- Z = ( ( P .\/ Q ) ./\ ( C .\/ ( ( R .\/ S ) ./\ W ) ) )
  assume cdleme43.d: |- D = ( ( S .\/ X ) ./\ ( P .\/ ( ( Q .\/ S ) ./\ W ) ) )
  assume cdleme43.g: |- G = ( ( Q .\/ P ) ./\ ( D .\/ ( ( Z .\/ S ) ./\ W ) ) )
  assume cdleme43.e: |- E = ( ( D .\/ U ) ./\ ( Q .\/ ( ( P .\/ D ) ./\ W ) ) )
  assume cdleme43.v: |- V = ( ( Z .\/ S ) ./\ W )
  assume cdleme43.y: |- Y = ( ( R .\/ D ) ./\ W )


  assert |- ( ( K e. HL /\ P e. A /\ Q e. A ) -> G = ( ( P .\/ Q ) ./\ ( D .\/ V ) ) )

  proof
    cK
    chlt
    wcel
    cP
    cA
    wcel
    cQ
    cA
    wcel
    w3a
    #
    cP
    cQ
    c.or
    co
    #
    cD
    cV
    c.or
    co
    #
    c.an
    co
    cQ
    cP
    c.or
    co
    #
    cD
    cZ
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
    cG
    @0
    @1
    @3
    @2
    @5
    c.an
    cA
    c.or
    cK
    cP
    cQ
    cdleme43.j
    cdleme43.a
    hlatjcom
    @2
    @5
    wceq
    @0
    cV
    @4
    cD
    c.or
    cdleme43.v
    oveq2i
    a1i
    oveq12d
    cdleme43.g
    syl6reqr
end
