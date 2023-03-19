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
include "simp31.mm"
include "simp23l.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latmle2.mm"
include "syl5eqbr.mm"
include "simp32.mm"
include "simp33.mm"
include "jca.mm"
include "cdleme3.mm"
include "syld3an3.mm"
include "nbrne2.mm"
include "syl2anc.mm"
include "necomd.mm"

theorem cdleme19c
  let cA: class A
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
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
  let cY: class Y
  assume cdleme19.l: |- .<_ = ( le ` K )
  assume cdleme19.j: |- .\/ = ( join ` K )
  assume cdleme19.m: |- ./\ = ( meet ` K )
  assume cdleme19.a: |- A = ( Atoms ` K )
  assume cdleme19.h: |- H = ( LHyp ` K )
  assume cdleme19.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme19.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme19.g: |- G = ( ( T .\/ U ) ./\ ( Q .\/ ( ( P .\/ T ) ./\ W ) ) )
  assume cdleme19.d: |- D = ( ( R .\/ S ) ./\ W )
  assume cdleme19.y: |- Y = ( ( R .\/ T ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( R e. A /\ P =/= Q /\ -. S .<_ ( P .\/ Q ) ) ) -> F =/= D )

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
    cP
    cW
    c.le
    wbr
    wn
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
    w3a
    #
    cR
    cA
    wcel
    #
    cP
    cQ
    wne
    #
    cS
    cP
    cQ
    c.or
    co
    c.le
    wbr
    wn
    #
    w3a
    #
    w3a
    #
    cD
    cF
    @12
    cD
    cW
    c.le
    wbr
    cF
    cW
    c.le
    wbr
    wn
    #
    cD
    cF
    wne
    @12
    cD
    cR
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
    cdleme19.d
    @12
    cK
    clat
    wcel
    #
    @14
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @17
    wcel
    #
    @15
    cW
    c.le
    wbr
    @12
    @0
    @16
    @0
    @1
    @7
    @11
    simp1l
    #
    cK
    hllat
    syl
    @12
    @0
    @8
    @5
    @18
    @20
    @2
    @7
    @8
    @9
    @10
    simp31
    @5
    @6
    @3
    @4
    @2
    @11
    simp23l
    cA
    @17
    c.or
    cK
    cR
    cS
    @17
    eqid
    #
    cdleme19.j
    cdleme19.a
    hlatjcl
    syl3anc
    @12
    @1
    @19
    @0
    @1
    @7
    @11
    simp1r
    @17
    cH
    cK
    cW
    @21
    cdleme19.h
    lhpbase
    syl
    @17
    cK
    c.le
    c.an
    @14
    cW
    @21
    cdleme19.l
    cdleme19.m
    latmle2
    syl3anc
    syl5eqbr
    @2
    @7
    @11
    @9
    @10
    wa
    @13
    @12
    @9
    @10
    @2
    @7
    @8
    @9
    @10
    simp32
    @2
    @7
    @8
    @9
    @10
    simp33
    jca
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
    cdleme19.l
    cdleme19.j
    cdleme19.m
    cdleme19.a
    cdleme19.h
    cdleme19.u
    cdleme19.f
    cdleme3
    syld3an3
    cD
    cF
    cW
    c.le
    nbrne2
    syl2anc
    necomd
end
