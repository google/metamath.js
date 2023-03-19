include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "eqid.mm"
include "oveq2.mm"
include "simp1l.mm"
include "simp22l.mm"
include "hlatjidm.mm"
include "syl2anc.mm"
include "sylan9eqr.mm"
include "simp1.mm"
include "simp21l.mm"
include "simp22.mm"
include "simp23.mm"
include "hlatlej2.mm"
include "syl3anc.mm"
include "cdleme5.mm"
include "syl132anc.mm"
include "adantr.mm"
include "eqtr3d.mm"
include "simp3l.mm"
include "2atneat.mm"
include "syl13anc.mm"
include "nelne2.mm"
include "necomd.mm"
include "eqnetrd.mm"
include "ex.mm"
include "necon2d.mm"
include "mpi.mm"

theorem cdleme18b
  let cA: class A
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
  assume cdleme18.l: |- .<_ = ( le ` K )
  assume cdleme18.j: |- .\/ = ( join ` K )
  assume cdleme18.m: |- ./\ = ( meet ` K )
  assume cdleme18.a: |- A = ( Atoms ` K )
  assume cdleme18.h: |- H = ( LHyp ` K )
  assume cdleme18.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme18.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme18.g: |- G = ( ( P .\/ Q ) ./\ ( F .\/ ( ( Q .\/ S ) ./\ W ) ) )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( P =/= Q /\ -. S .<_ ( P .\/ Q ) ) ) -> G =/= Q )

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
    cQ
    cW
    c.le
    wbr
    wn
    #
    wa
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
    #
    w3a
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
    #
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    cQ
    cQ
    wceq
    cG
    cQ
    wne
    cQ
    eqid
    @15
    cG
    cQ
    cQ
    cQ
    @15
    cG
    cQ
    wceq
    #
    cQ
    cQ
    wne
    @15
    @16
    wa
    #
    cQ
    @12
    cQ
    @17
    cQ
    cG
    c.or
    co
    #
    cQ
    @12
    @16
    @15
    @18
    cQ
    cQ
    c.or
    co
    #
    cQ
    cG
    cQ
    cQ
    c.or
    oveq2
    @15
    @0
    @6
    @19
    cQ
    wceq
    @0
    @1
    @10
    @14
    simp1l
    #
    @6
    @7
    @5
    @9
    @2
    @14
    simp22l
    #
    cA
    c.or
    cK
    cQ
    cdleme18.j
    cdleme18.a
    hlatjidm
    syl2anc
    sylan9eqr
    @15
    @18
    @12
    wceq
    #
    @16
    @15
    @2
    @3
    @6
    @8
    @9
    cQ
    @12
    c.le
    wbr
    #
    @22
    @2
    @10
    @14
    simp1
    @3
    @4
    @8
    @9
    @2
    @14
    simp21l
    #
    @21
    @2
    @5
    @8
    @9
    @14
    simp22
    @2
    @5
    @8
    @9
    @14
    simp23
    @15
    @0
    @3
    @6
    @23
    @20
    @24
    @21
    cA
    cP
    cQ
    c.or
    cK
    c.le
    cdleme18.l
    cdleme18.j
    cdleme18.a
    hlatlej2
    syl3anc
    cA
    cP
    cQ
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
    cdleme18.l
    cdleme18.j
    cdleme18.m
    cdleme18.a
    cdleme18.h
    cdleme18.u
    cdleme18.f
    cdleme18.g
    cdleme5
    syl132anc
    adantr
    eqtr3d
    @15
    @12
    cQ
    wne
    #
    @16
    @15
    @6
    @12
    cA
    wcel
    wn
    #
    @25
    @21
    @15
    @0
    @3
    @6
    @11
    @26
    @20
    @24
    @21
    @2
    @10
    @11
    @13
    simp3l
    cA
    cP
    cQ
    c.or
    cK
    cdleme18.j
    cdleme18.a
    2atneat
    syl13anc
    @6
    @26
    wa
    cQ
    @12
    cQ
    @12
    cA
    nelne2
    necomd
    syl2anc
    adantr
    eqnetrd
    ex
    necon2d
    mpi
end
