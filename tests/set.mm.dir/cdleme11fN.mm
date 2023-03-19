include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp21l.mm"
include "eqid.mm"
include "atbase.mm"
include "simp23l.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latmle2.mm"
include "syl5eqbr.mm"
include "cdleme3.mm"
include "nbrne2.mm"
include "necomd.mm"
include "syl2anc.mm"

theorem cdleme11fN
  let cA: class A
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdleme11.l: |- .<_ = ( le ` K )
  assume cdleme11.j: |- .\/ = ( join ` K )
  assume cdleme11.m: |- ./\ = ( meet ` K )
  assume cdleme11.a: |- A = ( Atoms ` K )
  assume cdleme11.h: |- H = ( LHyp ` K )
  assume cdleme11.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme11.c: |- C = ( ( P .\/ S ) ./\ W )
  assume cdleme11.d: |- D = ( ( P .\/ T ) ./\ W )
  assume cdleme11.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( P =/= Q /\ -. S .<_ ( P .\/ Q ) ) ) -> F =/= C )

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
    cQ
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
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    cP
    cQ
    wne
    cS
    cP
    cQ
    c.or
    co
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    cC
    cW
    c.le
    wbr
    #
    cF
    cW
    c.le
    wbr
    wn
    #
    cF
    cC
    wne
    @12
    cC
    cP
    cS
    c.or
    co
    #
    cW
    c.an
    co
    #
    cW
    c.le
    cdleme11.c
    @12
    cK
    clat
    wcel
    #
    @15
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @18
    wcel
    #
    @16
    cW
    c.le
    wbr
    @12
    @0
    @17
    @0
    @1
    @10
    @11
    simp1l
    cK
    hllat
    syl
    #
    @12
    @17
    cP
    @18
    wcel
    #
    cS
    @18
    wcel
    #
    @19
    @21
    @12
    @3
    @22
    @3
    @4
    @6
    @9
    @2
    @11
    simp21l
    cA
    @18
    cP
    cK
    @18
    eqid
    #
    cdleme11.a
    atbase
    syl
    @12
    @7
    @23
    @7
    @8
    @5
    @6
    @2
    @11
    simp23l
    cA
    @18
    cS
    cK
    @24
    cdleme11.a
    atbase
    syl
    @18
    c.or
    cK
    cP
    cS
    @24
    cdleme11.j
    latjcl
    syl3anc
    @12
    @1
    @20
    @0
    @1
    @10
    @11
    simp1r
    @18
    cH
    cK
    cW
    @24
    cdleme11.h
    lhpbase
    syl
    @18
    cK
    c.le
    c.an
    @15
    cW
    @24
    cdleme11.l
    cdleme11.m
    latmle2
    syl3anc
    syl5eqbr
    cA
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
    cdleme11.l
    cdleme11.j
    cdleme11.m
    cdleme11.a
    cdleme11.h
    cdleme11.u
    cdleme11.f
    cdleme3
    @13
    @14
    wa
    cC
    cF
    cC
    cF
    cW
    c.le
    nbrne2
    necomd
    syl2anc
end
