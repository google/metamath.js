include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "cdleme7a.mm"
include "cdleme9.mm"
include "oveq2d.mm"
include "syl5eq.mm"

theorem cdleme17a
  let cA: class A
  let cC: class C
  let cP: class P
  let cQ: class Q
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
  assume cdleme17.l: |- .<_ = ( le ` K )
  assume cdleme17.j: |- .\/ = ( join ` K )
  assume cdleme17.m: |- ./\ = ( meet ` K )
  assume cdleme17.a: |- A = ( Atoms ` K )
  assume cdleme17.h: |- H = ( LHyp ` K )
  assume cdleme17.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme17.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme17.g: |- G = ( ( P .\/ Q ) ./\ ( F .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme17.c: |- C = ( ( P .\/ S ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ Q e. A /\ ( S e. A /\ -. S .<_ W ) ) /\ -. S .<_ ( P .\/ Q ) ) -> G = ( ( P .\/ Q ) ./\ ( Q .\/ C ) ) )

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
    cS
    cA
    wcel
    cS
    cW
    c.le
    wbr
    wn
    wa
    w3a
    cS
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    wn
    w3a
    #
    cG
    @0
    cF
    cC
    c.or
    co
    #
    c.an
    co
    @0
    cQ
    cC
    c.or
    co
    #
    c.an
    co
    cA
    cP
    cQ
    cP
    cS
    cU
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cC
    cW
    cdleme17.l
    cdleme17.j
    cdleme17.m
    cdleme17.a
    cdleme17.h
    cdleme17.u
    cdleme17.f
    cdleme17.g
    cdleme17.c
    cdleme7a
    @1
    @2
    @3
    @0
    c.an
    cA
    cC
    cP
    cQ
    cS
    cU
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme17.l
    cdleme17.j
    cdleme17.m
    cdleme17.a
    cdleme17.h
    cdleme17.u
    cdleme17.f
    cdleme17.c
    cdleme9
    oveq2d
    syl5eq
end
