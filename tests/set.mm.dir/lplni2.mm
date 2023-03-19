include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "simp2.mm"
include "simp3l.mm"
include "simp3r.mm"
include "eqidd.mm"
include "neeq1.mm"
include "oveq1.mm"
include "breq2d.mm"
include "notbid.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "3anbi123d.mm"
include "neeq2.mm"
include "oveq2.mm"
include "breq1.mm"
include "3anbi23d.mm"
include "rspc3ev.mm"
include "syl13anc.mm"
include "cbs.mm"
include "cfv.mm"
include "wb.mm"
include "simp1.mm"
include "clat.mm"
include "hllat.mm"
include "3ad2ant1.mm"
include "simp21.mm"
include "simp22.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp23.mm"
include "atbase.mm"
include "syl.mm"
include "latjcl.mm"
include "islpln5.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem lplni2
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let vq: setvar q
  let vr: setvar r
  let vs: setvar s
  assume lplni2.l: |- .<_ = ( le ` K )
  assume lplni2.j: |- .\/ = ( join ` K )
  assume lplni2.a: |- A = ( Atoms ` K )
  assume lplni2.p: |- P = ( LPlanes ` K )


  assert |- ( ( K e. HL /\ ( Q e. A /\ R e. A /\ S e. A ) /\ ( Q =/= R /\ -. S .<_ ( Q .\/ R ) ) ) -> ( ( Q .\/ R ) .\/ S ) e. P )

  proof
    cK
    chlt
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
    cS
    cA
    wcel
    #
    w3a
    #
    cQ
    cR
    wne
    #
    cS
    cQ
    cR
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    wa
    #
    w3a
    #
    @6
    cS
    c.or
    co
    #
    cP
    wcel
    #
    vq
    cv
    #
    vr
    cv
    #
    wne
    #
    vs
    cv
    #
    @13
    @14
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    @11
    @17
    @16
    c.or
    co
    #
    wceq
    #
    w3a
    #
    vs
    cA
    wrex
    vr
    cA
    wrex
    vq
    cA
    wrex
    #
    @10
    @4
    @5
    @8
    @11
    @11
    wceq
    #
    @23
    @0
    @4
    @9
    simp2
    @0
    @4
    @5
    @8
    simp3l
    @0
    @4
    @5
    @8
    simp3r
    @10
    @11
    eqidd
    @22
    @5
    @8
    @24
    w3a
    cQ
    @14
    wne
    #
    @16
    cQ
    @14
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    @11
    @26
    @16
    c.or
    co
    #
    wceq
    #
    w3a
    @5
    @16
    @6
    c.le
    wbr
    #
    wn
    #
    @11
    @6
    @16
    c.or
    co
    #
    wceq
    #
    w3a
    vq
    vr
    vs
    cQ
    cR
    cS
    cA
    cA
    cA
    @13
    cQ
    wceq
    #
    @15
    @25
    @19
    @28
    @21
    @30
    @13
    cQ
    @14
    neeq1
    @35
    @18
    @27
    @35
    @17
    @26
    @16
    c.le
    @13
    cQ
    @14
    c.or
    oveq1
    #
    breq2d
    notbid
    @35
    @20
    @29
    @11
    @35
    @17
    @26
    @16
    c.or
    @36
    oveq1d
    eqeq2d
    3anbi123d
    @14
    cR
    wceq
    #
    @25
    @5
    @28
    @32
    @30
    @34
    @14
    cR
    cQ
    neeq2
    @37
    @27
    @31
    @37
    @26
    @6
    @16
    c.le
    @14
    cR
    cQ
    c.or
    oveq2
    #
    breq2d
    notbid
    @37
    @29
    @33
    @11
    @37
    @26
    @6
    @16
    c.or
    @38
    oveq1d
    eqeq2d
    3anbi123d
    @16
    cS
    wceq
    #
    @32
    @8
    @34
    @24
    @5
    @39
    @31
    @7
    @16
    cS
    @6
    c.le
    breq1
    notbid
    @39
    @33
    @11
    @11
    @16
    cS
    @6
    c.or
    oveq2
    eqeq2d
    3anbi23d
    rspc3ev
    syl13anc
    @10
    @0
    @11
    cK
    cbs
    cfv
    #
    wcel
    #
    @12
    @23
    wb
    @0
    @4
    @9
    simp1
    #
    @10
    cK
    clat
    wcel
    #
    @6
    @40
    wcel
    #
    cS
    @40
    wcel
    #
    @41
    @0
    @4
    @43
    @9
    cK
    hllat
    3ad2ant1
    @10
    @0
    @1
    @2
    @44
    @42
    @0
    @1
    @2
    @3
    @9
    simp21
    @0
    @1
    @2
    @3
    @9
    simp22
    cA
    @40
    c.or
    cK
    cQ
    cR
    @40
    eqid
    #
    lplni2.j
    lplni2.a
    hlatjcl
    syl3anc
    @10
    @3
    @45
    @0
    @1
    @2
    @3
    @9
    simp23
    cA
    @40
    cS
    cK
    @46
    lplni2.a
    atbase
    syl
    @40
    c.or
    cK
    @6
    cS
    @46
    lplni2.j
    latjcl
    syl3anc
    cA
    @40
    cP
    c.or
    cK
    c.le
    @11
    vs
    vr
    vq
    @46
    lplni2.l
    lplni2.j
    lplni2.a
    lplni2.p
    islpln5
    syl2anc
    mpbird
end
