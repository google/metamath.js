include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "simp1.mm"
include "simp2.mm"
include "simp32.mm"
include "simp33.mm"
include "cdleme11c.mm"
include "syl112anc.mm"
include "wceq.mm"
include "simp11l.mm"
include "simp12l.mm"
include "simp21l.mm"
include "hlatlej2.mm"
include "syl3anc.mm"
include "breq2.mm"
include "syl5ibcom.mm"
include "wi.mm"
include "simp22.mm"
include "simp31.mm"
include "hlatexch2.mm"
include "syl131anc.mm"
include "syld.mm"
include "necon3bd.mm"
include "mpd.mm"

theorem cdleme11dN
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ Q e. A ) /\ ( ( S e. A /\ -. S .<_ W ) /\ T e. A /\ P =/= Q ) /\ ( S =/= T /\ -. S .<_ ( P .\/ Q ) /\ U .<_ ( S .\/ T ) ) ) -> ( P .\/ S ) =/= ( P .\/ T ) )

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
    w3a
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
    cT
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
    cT
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
    cU
    cS
    cT
    c.or
    co
    #
    c.le
    wbr
    #
    w3a
    #
    w3a
    #
    cP
    @16
    c.le
    wbr
    #
    wn
    #
    cP
    cS
    c.or
    co
    #
    cP
    cT
    c.or
    co
    #
    wne
    @19
    @7
    @13
    @15
    @17
    @21
    @7
    @13
    @18
    simp1
    @7
    @13
    @18
    simp2
    @7
    @13
    @14
    @15
    @17
    simp32
    @7
    @13
    @14
    @15
    @17
    simp33
    cA
    cP
    cQ
    cS
    cT
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
    cdleme11c
    syl112anc
    @19
    @20
    @22
    @23
    @19
    @22
    @23
    wceq
    #
    cS
    @23
    c.le
    wbr
    #
    @20
    @19
    cS
    @22
    c.le
    wbr
    #
    @24
    @25
    @19
    @0
    @3
    @8
    @26
    @0
    @1
    @5
    @6
    @13
    @18
    simp11l
    #
    @3
    @4
    @2
    @6
    @13
    @18
    simp12l
    #
    @8
    @9
    @11
    @12
    @7
    @18
    simp21l
    #
    cA
    cP
    cS
    c.or
    cK
    c.le
    cdleme11.l
    cdleme11.j
    cdleme11.a
    hlatlej2
    syl3anc
    @22
    @23
    cS
    c.le
    breq2
    syl5ibcom
    @19
    @0
    @8
    @3
    @11
    @14
    @25
    @20
    wi
    @27
    @29
    @28
    @7
    @10
    @11
    @12
    @18
    simp22
    @7
    @13
    @14
    @15
    @17
    simp31
    cA
    cS
    cP
    cT
    c.or
    cK
    c.le
    cdleme11.l
    cdleme11.j
    cdleme11.a
    hlatexch2
    syl131anc
    syld
    necon3bd
    mpd
end
