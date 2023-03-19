include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "simp11.mm"
include "simp12.mm"
include "simp22.mm"
include "simp21.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp12l.mm"
include "eqid.mm"
include "atbase.mm"
include "simp21l.mm"
include "simp1.mm"
include "simp2.mm"
include "simp32.mm"
include "simp33.mm"
include "cdleme11c.mm"
include "syl112anc.mm"
include "latnlej1r.mm"
include "syl131anc.mm"
include "simp31.mm"
include "hlatcon2.mm"
include "syl132anc.mm"
include "cdleme0e.mm"
include "necomd.mm"

theorem cdleme11e
  let cA: class A
  let cC: class C
  let cD: class D
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
  assume cdleme11.c: |- C = ( ( P .\/ S ) ./\ W )
  assume cdleme11.d: |- D = ( ( P .\/ T ) ./\ W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ Q e. A ) /\ ( ( S e. A /\ -. S .<_ W ) /\ T e. A /\ P =/= Q ) /\ ( S =/= T /\ -. S .<_ ( P .\/ Q ) /\ U .<_ ( S .\/ T ) ) ) -> C =/= D )

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
    cD
    cC
    @19
    @2
    @5
    @11
    @10
    cP
    cT
    wne
    #
    cS
    cP
    cT
    c.or
    co
    c.le
    wbr
    wn
    #
    cD
    cC
    wne
    @2
    @5
    @6
    @13
    @18
    simp11
    @2
    @5
    @6
    @13
    @18
    simp12
    @7
    @10
    @11
    @12
    @18
    simp22
    #
    @7
    @10
    @11
    @12
    @18
    simp21
    @19
    cK
    clat
    wcel
    #
    cP
    cK
    cbs
    cfv
    #
    wcel
    #
    cS
    @24
    wcel
    #
    cT
    @24
    wcel
    #
    cP
    @16
    c.le
    wbr
    wn
    #
    @20
    @19
    @0
    @23
    @0
    @1
    @5
    @6
    @13
    @18
    simp11l
    #
    cK
    hllat
    syl
    @19
    @3
    @25
    @3
    @4
    @2
    @6
    @13
    @18
    simp12l
    #
    cA
    @24
    cP
    cK
    @24
    eqid
    #
    cdleme11.a
    atbase
    syl
    @19
    @8
    @26
    @8
    @9
    @11
    @12
    @7
    @18
    simp21l
    #
    cA
    @24
    cS
    cK
    @31
    cdleme11.a
    atbase
    syl
    @19
    @11
    @27
    @22
    cA
    @24
    cT
    cK
    @31
    cdleme11.a
    atbase
    syl
    @19
    @7
    @13
    @15
    @17
    @28
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
    #
    @24
    c.or
    cK
    c.le
    cP
    cS
    cT
    @31
    cdleme11.l
    cdleme11.j
    latnlej1r
    syl131anc
    @19
    @0
    @8
    @11
    @3
    @14
    @28
    @21
    @29
    @32
    @22
    @30
    @7
    @13
    @14
    @15
    @17
    simp31
    @33
    cA
    cS
    cT
    cP
    c.or
    cK
    c.le
    cdleme11.l
    cdleme11.j
    cdleme11.a
    hlatcon2
    syl132anc
    cA
    cP
    cT
    cS
    cD
    cH
    c.or
    cK
    c.le
    c.an
    cC
    cW
    cdleme11.l
    cdleme11.j
    cdleme11.m
    cdleme11.a
    cdleme11.h
    cdleme11.d
    cdleme11.c
    cdleme0e
    syl132anc
    necomd
end
