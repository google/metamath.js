include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "cdleme5.mm"
include "oveq1d.mm"
include "syl6eqr.mm"

theorem cdleme6
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
  let cW: class W
  assume cdleme4.l: |- .<_ = ( le ` K )
  assume cdleme4.j: |- .\/ = ( join ` K )
  assume cdleme4.m: |- ./\ = ( meet ` K )
  assume cdleme4.a: |- A = ( Atoms ` K )
  assume cdleme4.h: |- H = ( LHyp ` K )
  assume cdleme4.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme4.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme4.g: |- G = ( ( P .\/ Q ) ./\ ( F .\/ ( ( R .\/ S ) ./\ W ) ) )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ Q e. A /\ ( R e. A /\ -. R .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ R .<_ ( P .\/ Q ) ) ) -> ( ( R .\/ G ) ./\ W ) = U )

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
    cQ
    cA
    wcel
    cR
    cA
    wcel
    cR
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
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    wa
    w3a
    #
    cR
    cG
    c.or
    co
    #
    cW
    c.an
    co
    @0
    cW
    c.an
    co
    cU
    @1
    @2
    @0
    cW
    c.an
    cA
    cP
    cQ
    cR
    cS
    cU
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme4.l
    cdleme4.j
    cdleme4.m
    cdleme4.a
    cdleme4.h
    cdleme4.u
    cdleme4.f
    cdleme4.g
    cdleme5
    oveq1d
    cdleme4.u
    syl6eqr
end
