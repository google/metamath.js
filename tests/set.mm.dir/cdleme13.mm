include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "w3a.mm"
include "co.mm"
include "cdleme12.mm"
include "syl6eq.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp21l.mm"
include "simp22.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latmle1.mm"
include "eqbrtrd.mm"

theorem cdleme13
  let cA: class A
  let cP: class P
  let cQ: class Q
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
  let cW: class W
  assume cdleme12.l: |- .<_ = ( le ` K )
  assume cdleme12.j: |- .\/ = ( join ` K )
  assume cdleme12.m: |- ./\ = ( meet ` K )
  assume cdleme12.a: |- A = ( Atoms ` K )
  assume cdleme12.h: |- H = ( LHyp ` K )
  assume cdleme12.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme12.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme12.g: |- G = ( ( T .\/ U ) ./\ ( Q .\/ ( ( P .\/ T ) ./\ W ) ) )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ Q e. A /\ P =/= Q ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) /\ ( S =/= T /\ -. U .<_ ( S .\/ T ) ) ) ) -> ( ( S .\/ F ) ./\ ( T .\/ G ) ) .<_ ( P .\/ Q ) )

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
    cP
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cQ
    cA
    wcel
    #
    cP
    cQ
    wne
    #
    w3a
    #
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
    cS
    cT
    wne
    cU
    cS
    cT
    c.or
    co
    c.le
    wbr
    wn
    wa
    w3a
    #
    w3a
    #
    cS
    cF
    c.or
    co
    cT
    cG
    c.or
    co
    c.an
    co
    #
    cP
    cQ
    c.or
    co
    #
    cW
    c.an
    co
    #
    @12
    c.le
    @10
    @11
    cU
    @13
    cA
    cP
    cQ
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
    cdleme12.l
    cdleme12.j
    cdleme12.m
    cdleme12.a
    cdleme12.h
    cdleme12.u
    cdleme12.f
    cdleme12.g
    cdleme12
    cdleme12.u
    syl6eq
    @10
    cK
    clat
    wcel
    #
    @12
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @15
    wcel
    #
    @13
    @12
    c.le
    wbr
    @10
    @0
    @14
    @0
    @1
    @8
    @9
    simp1l
    #
    cK
    hllat
    syl
    @10
    @0
    @3
    @6
    @16
    @18
    @3
    @4
    @6
    @7
    @2
    @9
    simp21l
    @2
    @5
    @6
    @7
    @9
    simp22
    cA
    @15
    c.or
    cK
    cP
    cQ
    @15
    eqid
    #
    cdleme12.j
    cdleme12.a
    hlatjcl
    syl3anc
    @10
    @1
    @17
    @0
    @1
    @8
    @9
    simp1r
    @15
    cH
    cK
    cW
    @19
    cdleme12.h
    lhpbase
    syl
    @15
    cK
    c.le
    c.an
    @12
    cW
    @19
    cdleme12.l
    cdleme12.m
    latmle1
    syl3anc
    eqbrtrd
end
