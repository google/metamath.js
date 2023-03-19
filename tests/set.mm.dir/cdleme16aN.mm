include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "clpl.mm"
include "cfv.mm"
include "simp1ll.mm"
include "simp22.mm"
include "simp23.mm"
include "simp1l.mm"
include "simp1r.mm"
include "simp21.mm"
include "simp31.mm"
include "lhpat2.mm"
include "syl112anc.mm"
include "simp32.mm"
include "simp33.mm"
include "eqid.mm"
include "lplni2.mm"
include "syl132anc.mm"
include "lplnllnneN.mm"
include "syl131anc.mm"

theorem cdleme16aN
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cT: class T
  let cU: class U
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) ) /\ ( Q e. A /\ S e. A /\ T e. A ) /\ ( P =/= Q /\ S =/= T /\ -. U .<_ ( S .\/ T ) ) ) -> ( S .\/ U ) =/= ( T .\/ U ) )

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
    cT
    cA
    wcel
    #
    w3a
    #
    cP
    cQ
    wne
    #
    cS
    cT
    wne
    #
    cU
    cS
    cT
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
    @0
    @6
    @7
    cU
    cA
    wcel
    #
    @11
    cU
    c.or
    co
    #
    cK
    clpl
    cfv
    #
    wcel
    #
    cS
    cU
    c.or
    co
    cT
    cU
    c.or
    co
    wne
    @0
    @1
    @3
    @8
    @13
    simp1ll
    #
    @4
    @5
    @6
    @7
    @13
    simp22
    #
    @4
    @5
    @6
    @7
    @13
    simp23
    #
    @14
    @2
    @3
    @5
    @9
    @15
    @2
    @3
    @8
    @13
    simp1l
    @2
    @3
    @8
    @13
    simp1r
    @4
    @5
    @6
    @7
    @13
    simp21
    @4
    @8
    @9
    @10
    @12
    simp31
    cA
    cP
    cQ
    cU
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
    lhpat2
    syl112anc
    #
    @14
    @0
    @6
    @7
    @15
    @10
    @12
    @18
    @19
    @20
    @21
    @22
    @4
    @8
    @9
    @10
    @12
    simp32
    @4
    @8
    @9
    @10
    @12
    simp33
    cA
    @17
    cS
    cT
    cU
    c.or
    cK
    c.le
    cdleme11.l
    cdleme11.j
    cdleme11.a
    @17
    eqid
    #
    lplni2
    syl132anc
    cA
    @17
    cS
    cT
    cU
    c.or
    cK
    @16
    cdleme11.j
    cdleme11.a
    @23
    @16
    eqid
    lplnllnneN
    syl131anc
end
