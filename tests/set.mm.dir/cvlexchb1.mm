include "clc.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "clat.mm"
include "cvllat.mm"
include "adantr.mm"
include "simpr3.mm"
include "simpr2.mm"
include "atbase.mm"
include "syl.mm"
include "latlej1.mm"
include "syl3anc.mm"
include "3adant3.mm"
include "simpr.mm"
include "wb.mm"
include "simpr1.mm"
include "latjcl.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "cvlexch1.mm"
include "imp.mm"
include "latasymb.mm"
include "ex.mm"
include "wi.mm"
include "latlej2.mm"
include "breq2.mm"
include "syl5ibcom.mm"
include "impbid.mm"

theorem cvlexchb1
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let vp: setvar p
  let vq: setvar q
  let vx: setvar x
  assume cvlexch.b: |- B = ( Base ` K )
  assume cvlexch.l: |- .<_ = ( le ` K )
  assume cvlexch.j: |- .\/ = ( join ` K )
  assume cvlexch.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. CvLat /\ ( P e. A /\ Q e. A /\ X e. B ) /\ -. P .<_ X ) -> ( P .<_ ( X .\/ Q ) <-> ( X .\/ P ) = ( X .\/ Q ) ) )

  proof
    cK
    clc
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
    cX
    cB
    wcel
    #
    w3a
    #
    cP
    cX
    c.le
    wbr
    wn
    #
    w3a
    #
    cP
    cX
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    cX
    cP
    c.or
    co
    #
    @7
    wceq
    #
    @6
    @8
    @10
    @6
    @8
    wa
    #
    @9
    @7
    c.le
    wbr
    #
    @7
    @9
    c.le
    wbr
    #
    @10
    @11
    cX
    @7
    c.le
    wbr
    #
    @8
    @12
    @6
    @14
    @8
    @0
    @4
    @14
    @5
    @0
    @4
    wa
    #
    cK
    clat
    wcel
    #
    @3
    cQ
    cB
    wcel
    #
    @14
    @0
    @16
    @4
    cK
    cvllat
    adantr
    #
    @0
    @1
    @2
    @3
    simpr3
    #
    @15
    @2
    @17
    @0
    @1
    @2
    @3
    simpr2
    cA
    cB
    cQ
    cK
    cvlexch.b
    cvlexch.a
    atbase
    syl
    #
    cB
    c.or
    cK
    c.le
    cX
    cQ
    cvlexch.b
    cvlexch.l
    cvlexch.j
    latlej1
    syl3anc
    3adant3
    adantr
    @6
    @8
    simpr
    @6
    @14
    @8
    wa
    @12
    wb
    #
    @8
    @0
    @4
    @21
    @5
    @15
    @16
    @3
    cP
    cB
    wcel
    #
    @7
    cB
    wcel
    #
    @21
    @18
    @19
    @15
    @1
    @22
    @0
    @1
    @2
    @3
    simpr1
    cA
    cB
    cP
    cK
    cvlexch.b
    cvlexch.a
    atbase
    syl
    #
    @15
    @16
    @3
    @17
    @23
    @18
    @19
    @20
    cB
    c.or
    cK
    cX
    cQ
    cvlexch.b
    cvlexch.j
    latjcl
    syl3anc
    #
    cB
    c.or
    cK
    c.le
    cX
    cP
    @7
    cvlexch.b
    cvlexch.l
    cvlexch.j
    latjle12
    syl13anc
    3adant3
    adantr
    mpbi2and
    @11
    cX
    @9
    c.le
    wbr
    #
    cQ
    @9
    c.le
    wbr
    #
    @13
    @6
    @26
    @8
    @0
    @4
    @26
    @5
    @15
    @16
    @3
    @22
    @26
    @18
    @19
    @24
    cB
    c.or
    cK
    c.le
    cX
    cP
    cvlexch.b
    cvlexch.l
    cvlexch.j
    latlej1
    syl3anc
    3adant3
    adantr
    @6
    @8
    @27
    cA
    cB
    cP
    cQ
    c.or
    cK
    c.le
    cX
    cvlexch.b
    cvlexch.l
    cvlexch.j
    cvlexch.a
    cvlexch1
    imp
    @6
    @26
    @27
    wa
    @13
    wb
    #
    @8
    @0
    @4
    @28
    @5
    @15
    @16
    @3
    @17
    @9
    cB
    wcel
    #
    @28
    @18
    @19
    @20
    @15
    @16
    @3
    @22
    @29
    @18
    @19
    @24
    cB
    c.or
    cK
    cX
    cP
    cvlexch.b
    cvlexch.j
    latjcl
    syl3anc
    #
    cB
    c.or
    cK
    c.le
    cX
    cQ
    @9
    cvlexch.b
    cvlexch.l
    cvlexch.j
    latjle12
    syl13anc
    3adant3
    adantr
    mpbi2and
    @6
    @12
    @13
    wa
    @10
    wb
    #
    @8
    @0
    @4
    @31
    @5
    @15
    @16
    @29
    @23
    @31
    @18
    @30
    @25
    cB
    cK
    c.le
    @9
    @7
    cvlexch.b
    cvlexch.l
    latasymb
    syl3anc
    3adant3
    adantr
    mpbi2and
    ex
    @0
    @4
    @10
    @8
    wi
    @5
    @15
    cP
    @9
    c.le
    wbr
    #
    @10
    @8
    @15
    @16
    @3
    @22
    @32
    @18
    @19
    @24
    cB
    c.or
    cK
    c.le
    cX
    cP
    cvlexch.b
    cvlexch.l
    cvlexch.j
    latlej2
    syl3anc
    @9
    @7
    cP
    c.le
    breq2
    syl5ibcom
    3adant3
    impbid
end
