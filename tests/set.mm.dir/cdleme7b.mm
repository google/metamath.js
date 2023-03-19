include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "w3a.mm"
include "wne.mm"
include "simp1.mm"
include "simp2.mm"
include "simp31.mm"
include "simp33.mm"
include "simp32.mm"
include "nbrne2.mm"
include "syl2anc.mm"
include "lhpat.mm"
include "syl112anc.mm"
include "syl5eqel.mm"

theorem cdleme7b
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ ( P .\/ Q ) /\ R .<_ ( P .\/ Q ) ) ) -> V e. A )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
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
    #
    cS
    cA
    wcel
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
    cR
    @3
    c.le
    wbr
    #
    w3a
    #
    w3a
    #
    cV
    cR
    cS
    c.or
    co
    cW
    c.an
    co
    #
    cA
    cdleme7.v
    @7
    @0
    @1
    @2
    cR
    cS
    wne
    #
    @8
    cA
    wcel
    @0
    @1
    @6
    simp1
    @0
    @1
    @6
    simp2
    @0
    @1
    @2
    @4
    @5
    simp31
    @7
    @5
    @4
    @9
    @0
    @1
    @2
    @4
    @5
    simp33
    @0
    @1
    @2
    @4
    @5
    simp32
    cR
    cS
    @3
    c.le
    nbrne2
    syl2anc
    cA
    cR
    cS
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
    lhpat
    syl112anc
    syl5eqel
end
