include "co.mm"
include "oveq2i.mm"
include "eqtr4i.mm"

theorem cdleme7a
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cW: class W
  assume cdleme4.l: |- .<_ = ( le ` K )
  assume cdleme4.j: |- .\/ = ( join ` K )
  assume cdleme4.m: |- ./\ = ( meet ` K )
  assume cdleme4.a: |- A = ( Atoms ` K )
  assume cdleme4.h: |- H = ( LHyp ` K )
  assume cdleme4.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme4.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme4.g: |- G = ( ( P .\/ Q ) ./\ ( F .\/ ( ( R .\/ S ) ./\ W ) ) )
  assume cdleme7.v: |- V = ( ( R .\/ S ) ./\ W )


  assert |- G = ( ( P .\/ Q ) ./\ ( F .\/ V ) )

  proof
    cG
    cP
    cQ
    c.or
    co
    #
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
    @0
    cF
    cV
    c.or
    co
    #
    c.an
    co
    cdleme4.g
    @3
    @2
    @0
    c.an
    cV
    @1
    cF
    c.or
    cdleme7.v
    oveq2i
    oveq2i
    eqtr4i
end
