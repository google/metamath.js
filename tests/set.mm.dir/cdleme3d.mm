include "co.mm"
include "oveq2i.mm"
include "eqtr4i.mm"

theorem cdleme3d
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cW: class W
  assume cdleme1.l: |- .<_ = ( le ` K )
  assume cdleme1.j: |- .\/ = ( join ` K )
  assume cdleme1.m: |- ./\ = ( meet ` K )
  assume cdleme1.a: |- A = ( Atoms ` K )
  assume cdleme1.h: |- H = ( LHyp ` K )
  assume cdleme1.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme1.f: |- F = ( ( R .\/ U ) ./\ ( Q .\/ ( ( P .\/ R ) ./\ W ) ) )
  assume cdleme3.3: |- V = ( ( P .\/ R ) ./\ W )


  assert |- F = ( ( R .\/ U ) ./\ ( Q .\/ V ) )

  proof
    cF
    cR
    cU
    c.or
    co
    #
    cQ
    cP
    cR
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
    cQ
    cV
    c.or
    co
    #
    c.an
    co
    cdleme1.f
    @3
    @2
    @0
    c.an
    cV
    @1
    cQ
    c.or
    cdleme3.3
    oveq2i
    oveq2i
    eqtr4i
end
