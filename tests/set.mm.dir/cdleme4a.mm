include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "wbr.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp21.mm"
include "simp22.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp1r.mm"
include "simp3.mm"
include "cdleme1b.mm"
include "syl23anc.mm"
include "simp23.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "latjcl.mm"
include "latmle1.mm"
include "syl5eqbr.mm"

theorem cdleme4a
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ Q e. A /\ R e. A ) /\ S e. A ) -> G .<_ ( P .\/ Q ) )

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
    cR
    cA
    wcel
    #
    w3a
    #
    cS
    cA
    wcel
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
    @9
    c.le
    cdleme4.g
    @8
    cK
    clat
    wcel
    #
    @9
    cK
    cbs
    cfv
    #
    wcel
    #
    @12
    @15
    wcel
    #
    @13
    @9
    c.le
    wbr
    @8
    @0
    @14
    @0
    @1
    @6
    @7
    simp1l
    #
    cK
    hllat
    syl
    #
    @8
    @0
    @3
    @4
    @16
    @18
    @2
    @3
    @4
    @5
    @7
    simp21
    #
    @2
    @3
    @4
    @5
    @7
    simp22
    #
    cA
    @15
    c.or
    cK
    cP
    cQ
    @15
    eqid
    #
    cdleme4.j
    cdleme4.a
    hlatjcl
    syl3anc
    @8
    @14
    cF
    @15
    wcel
    #
    @11
    @15
    wcel
    #
    @17
    @19
    @8
    @0
    @1
    @3
    @4
    @7
    @23
    @18
    @0
    @1
    @6
    @7
    simp1r
    #
    @20
    @21
    @2
    @6
    @7
    simp3
    #
    cA
    @15
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
    cdleme4.l
    cdleme4.j
    cdleme4.m
    cdleme4.a
    cdleme4.h
    cdleme4.u
    cdleme4.f
    @22
    cdleme1b
    syl23anc
    @8
    @14
    @10
    @15
    wcel
    #
    cW
    @15
    wcel
    #
    @24
    @19
    @8
    @0
    @5
    @7
    @27
    @18
    @2
    @3
    @4
    @5
    @7
    simp23
    @26
    cA
    @15
    c.or
    cK
    cR
    cS
    @22
    cdleme4.j
    cdleme4.a
    hlatjcl
    syl3anc
    @8
    @1
    @28
    @25
    @15
    cH
    cK
    cW
    @22
    cdleme4.h
    lhpbase
    syl
    @15
    cK
    c.an
    @10
    cW
    @22
    cdleme4.m
    latmcl
    syl3anc
    @15
    c.or
    cK
    cF
    @11
    @22
    cdleme4.j
    latjcl
    syl3anc
    @15
    cK
    c.le
    c.an
    @9
    @12
    @22
    cdleme4.l
    cdleme4.m
    latmle1
    syl3anc
    syl5eqbr
end
