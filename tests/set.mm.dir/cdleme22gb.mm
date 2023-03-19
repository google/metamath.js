include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "clat.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp2l.mm"
include "simp2r.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp1.mm"
include "simp3r.mm"
include "cdleme1b.mm"
include "syl13anc.mm"
include "simp3l.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "latjcl.mm"
include "syl5eqel.mm"

theorem cdleme22gb
  let cA: class A
  let cB: class B
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
  let vr: setvar r
  let cD: class D
  let cT: class T
  assume cdleme18d.l: |- .<_ = ( le ` K )
  assume cdleme18d.j: |- .\/ = ( join ` K )
  assume cdleme18d.m: |- ./\ = ( meet ` K )
  assume cdleme18d.a: |- A = ( Atoms ` K )
  assume cdleme18d.h: |- H = ( LHyp ` K )
  assume cdleme18d.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme18d.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme18d.g: |- G = ( ( P .\/ Q ) ./\ ( F .\/ ( ( R .\/ S ) ./\ W ) ) )
  assume cdleme22.b: |- B = ( Base ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ Q e. A ) /\ ( R e. A /\ S e. A ) ) -> G e. B )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    wa
    #
    cR
    cA
    wcel
    #
    cS
    cA
    wcel
    #
    wa
    #
    w3a
    #
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
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    #
    cB
    cdleme18d.g
    @9
    cK
    clat
    wcel
    #
    @10
    cB
    wcel
    #
    @13
    cB
    wcel
    #
    @14
    cB
    wcel
    @9
    @0
    @15
    @0
    @1
    @5
    @8
    simp1l
    #
    cK
    hllat
    syl
    #
    @9
    @0
    @3
    @4
    @16
    @18
    @2
    @3
    @4
    @8
    simp2l
    #
    @2
    @3
    @4
    @8
    simp2r
    #
    cA
    cB
    c.or
    cK
    cP
    cQ
    cdleme22.b
    cdleme18d.j
    cdleme18d.a
    hlatjcl
    syl3anc
    @9
    @15
    cF
    cB
    wcel
    #
    @12
    cB
    wcel
    #
    @17
    @19
    @9
    @2
    @3
    @4
    @7
    @22
    @2
    @5
    @8
    simp1
    @20
    @21
    @2
    @5
    @6
    @7
    simp3r
    #
    cA
    cB
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
    cdleme18d.l
    cdleme18d.j
    cdleme18d.m
    cdleme18d.a
    cdleme18d.h
    cdleme18d.u
    cdleme18d.f
    cdleme22.b
    cdleme1b
    syl13anc
    @9
    @15
    @11
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    @23
    @19
    @9
    @0
    @6
    @7
    @25
    @18
    @2
    @5
    @6
    @7
    simp3l
    @24
    cA
    cB
    c.or
    cK
    cR
    cS
    cdleme22.b
    cdleme18d.j
    cdleme18d.a
    hlatjcl
    syl3anc
    @9
    @1
    @26
    @0
    @1
    @5
    @8
    simp1r
    cB
    cH
    cK
    cW
    cdleme22.b
    cdleme18d.h
    lhpbase
    syl
    cB
    cK
    c.an
    @11
    cW
    cdleme22.b
    cdleme18d.m
    latmcl
    syl3anc
    cB
    c.or
    cK
    cF
    @12
    cdleme22.b
    cdleme18d.j
    latjcl
    syl3anc
    cB
    cK
    c.an
    @10
    @13
    cdleme22.b
    cdleme18d.m
    latmcl
    syl3anc
    syl5eqel
end
