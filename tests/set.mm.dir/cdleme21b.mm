include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "simp23.mm"
include "clc.mm"
include "wi.mm"
include "simp11.mm"
include "hlcvl.mm"
include "syl.mm"
include "simp3l.mm"
include "simp13.mm"
include "simp12.mm"
include "simp21.mm"
include "atnlej1.mm"
include "necomd.mm"
include "syl131anc.mm"
include "simp3r.mm"
include "cvlsupr5.mm"
include "syl132anc.mm"
include "cvlatexch1.mm"
include "cvlsupr8.mm"
include "breq2d.mm"
include "sylibrd.mm"
include "simp22.mm"
include "syld.mm"
include "mtod.mm"

theorem cdleme21b
  let vz: setvar z
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  assume cdleme21a.l: |- .<_ = ( le ` K )
  assume cdleme21a.j: |- .\/ = ( join ` K )
  assume cdleme21a.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( S e. A /\ P =/= Q /\ -. S .<_ ( P .\/ Q ) ) /\ ( z e. A /\ ( P .\/ z ) = ( S .\/ z ) ) ) -> -. z .<_ ( P .\/ Q ) )

  proof
    cK
    chlt
    wcel
    #
    cP
    cA
    wcel
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
    #
    wn
    #
    w3a
    #
    vz
    cv
    #
    cA
    wcel
    #
    cP
    @10
    c.or
    co
    #
    cS
    @10
    c.or
    co
    wceq
    #
    wa
    #
    w3a
    #
    @10
    @6
    c.le
    wbr
    #
    @7
    @3
    @4
    @5
    @8
    @14
    simp23
    #
    @15
    @16
    cQ
    cP
    cS
    c.or
    co
    #
    c.le
    wbr
    #
    @7
    @15
    @16
    cQ
    @12
    c.le
    wbr
    #
    @19
    @15
    cK
    clc
    wcel
    #
    @11
    @2
    @1
    @10
    cP
    wne
    #
    @16
    @20
    wi
    @15
    @0
    @21
    @0
    @1
    @2
    @9
    @14
    simp11
    #
    cK
    hlcvl
    syl
    #
    @3
    @9
    @11
    @13
    simp3l
    #
    @0
    @1
    @2
    @9
    @14
    simp13
    #
    @0
    @1
    @2
    @9
    @14
    simp12
    #
    @15
    @21
    @1
    @4
    @11
    cP
    cS
    wne
    #
    @13
    @22
    @24
    @27
    @3
    @4
    @5
    @8
    @14
    simp21
    #
    @25
    @15
    @0
    @4
    @1
    @2
    @8
    @28
    @23
    @29
    @27
    @26
    @17
    @0
    @4
    @1
    @2
    w3a
    @8
    w3a
    cS
    cP
    cA
    cS
    cP
    cQ
    c.or
    cK
    c.le
    cdleme21a.l
    cdleme21a.j
    cdleme21a.a
    atnlej1
    necomd
    syl131anc
    #
    @3
    @9
    @11
    @13
    simp3r
    #
    cA
    cP
    cS
    @10
    c.or
    cK
    cdleme21a.a
    cdleme21a.j
    cvlsupr5
    syl132anc
    cA
    @10
    cQ
    cP
    c.or
    cK
    c.le
    cdleme21a.l
    cdleme21a.j
    cdleme21a.a
    cvlatexch1
    syl131anc
    @15
    @18
    @12
    cQ
    c.le
    @15
    @21
    @1
    @4
    @11
    @28
    @13
    @18
    @12
    wceq
    @24
    @27
    @29
    @25
    @30
    @31
    cA
    cP
    cS
    @10
    c.or
    cK
    cdleme21a.a
    cdleme21a.j
    cvlsupr8
    syl132anc
    breq2d
    sylibrd
    @15
    @21
    @2
    @4
    @1
    cQ
    cP
    wne
    @19
    @7
    wi
    @24
    @26
    @29
    @27
    @15
    cP
    cQ
    @3
    @4
    @5
    @8
    @14
    simp22
    necomd
    cA
    cQ
    cS
    cP
    c.or
    cK
    c.le
    cdleme21a.l
    cdleme21a.j
    cdleme21a.a
    cvlatexch1
    syl131anc
    syld
    mtod
end
