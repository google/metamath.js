include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "w3a.mm"
include "wceq.mm"
include "simp1l.mm"
include "simp2l.mm"
include "simp31.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "wne.mm"
include "simp1r.mm"
include "simp2r.mm"
include "simp32.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "hllat.mm"
include "syl.mm"
include "eqid.mm"
include "atbase.mm"
include "simp33.mm"
include "latnlej1l.mm"
include "necomd.mm"
include "syl131anc.mm"
include "cdleme9a.mm"
include "syl222anc.mm"
include "cdleme17b.mm"
include "2llnma1.mm"
include "eqtrd.mm"

theorem cdleme17c
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ S e. A /\ -. S .<_ ( P .\/ Q ) ) ) -> ( ( P .\/ Q ) ./\ ( Q .\/ C ) ) = Q )

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
    w3a
    #
    w3a
    #
    @8
    cQ
    cC
    c.or
    co
    #
    c.an
    co
    cQ
    cP
    c.or
    co
    #
    @12
    c.an
    co
    #
    cQ
    @11
    @8
    @13
    @12
    c.an
    @11
    @0
    @3
    @6
    @8
    @13
    wceq
    @0
    @1
    @5
    @10
    simp1l
    #
    @2
    @3
    @4
    @10
    simp2l
    #
    @2
    @5
    @6
    @7
    @9
    simp31
    #
    cA
    c.or
    cK
    cP
    cQ
    cdleme17.j
    cdleme17.a
    hlatjcom
    syl3anc
    oveq1d
    @11
    @0
    @3
    @6
    cC
    cA
    wcel
    #
    cC
    @8
    c.le
    wbr
    wn
    @14
    cQ
    wceq
    @15
    @16
    @17
    @11
    @0
    @1
    @3
    @4
    @7
    cP
    cS
    wne
    #
    @18
    @15
    @0
    @1
    @5
    @10
    simp1r
    @16
    @2
    @3
    @4
    @10
    simp2r
    @2
    @5
    @6
    @7
    @9
    simp32
    #
    @11
    cK
    clat
    wcel
    #
    cS
    cK
    cbs
    cfv
    #
    wcel
    #
    cP
    @22
    wcel
    #
    cQ
    @22
    wcel
    #
    @9
    @19
    @11
    @0
    @21
    @15
    cK
    hllat
    syl
    @11
    @7
    @23
    @20
    cA
    @22
    cS
    cK
    @22
    eqid
    #
    cdleme17.a
    atbase
    syl
    @11
    @3
    @24
    @16
    cA
    @22
    cP
    cK
    @26
    cdleme17.a
    atbase
    syl
    @11
    @6
    @25
    @17
    cA
    @22
    cQ
    cK
    @26
    cdleme17.a
    atbase
    syl
    @2
    @5
    @6
    @7
    @9
    simp33
    @21
    @23
    @24
    @25
    w3a
    @9
    w3a
    cS
    cP
    @22
    c.or
    cK
    c.le
    cS
    cP
    cQ
    @26
    cdleme17.l
    cdleme17.j
    latnlej1l
    necomd
    syl131anc
    cA
    cC
    cP
    cS
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
    cdleme17.c
    cdleme9a
    syl222anc
    cA
    cC
    cP
    cQ
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
    cdleme17.l
    cdleme17.j
    cdleme17.m
    cdleme17.a
    cdleme17.h
    cdleme17.u
    cdleme17.f
    cdleme17.g
    cdleme17.c
    cdleme17b
    cA
    cP
    cQ
    cC
    c.or
    cK
    c.le
    c.an
    cdleme17.l
    cdleme17.j
    cdleme17.m
    cdleme17.a
    2llnma1
    syl131anc
    eqtrd
end
