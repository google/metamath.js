include "clc.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "wi.mm"
include "cv.mm"
include "wa.mm"
include "wral.mm"
include "cal.mm"
include "iscvlat.mm"
include "simprbi.mm"
include "wceq.mm"
include "breq1.mm"
include "notbid.mm"
include "anbi12d.mm"
include "oveq2.mm"
include "breq2d.mm"
include "imbi12d.mm"
include "anbi2d.mm"
include "breq2.mm"
include "oveq1.mm"
include "rspc3v.mm"
include "mpan9.mm"
include "exp4b.mm"
include "3imp.mm"

theorem cvlexch1
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


  assert |- ( ( K e. CvLat /\ ( P e. A /\ Q e. A /\ X e. B ) /\ -. P .<_ X ) -> ( P .<_ ( X .\/ Q ) -> Q .<_ ( X .\/ P ) ) )

  proof
    cK
    clc
    wcel
    #
    cP
    cA
    wcel
    cQ
    cA
    wcel
    cX
    cB
    wcel
    w3a
    #
    cP
    cX
    c.le
    wbr
    #
    wn
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
    cQ
    cX
    cP
    c.or
    co
    #
    c.le
    wbr
    #
    wi
    @0
    @1
    @3
    @5
    @7
    @0
    vp
    cv
    #
    vx
    cv
    #
    c.le
    wbr
    #
    wn
    #
    @8
    @9
    vq
    cv
    #
    c.or
    co
    #
    c.le
    wbr
    #
    wa
    #
    @12
    @9
    @8
    c.or
    co
    #
    c.le
    wbr
    #
    wi
    #
    vx
    cB
    wral
    vq
    cA
    wral
    vp
    cA
    wral
    #
    @1
    @3
    @5
    wa
    #
    @7
    wi
    #
    @0
    cK
    cal
    wcel
    @19
    vx
    cA
    cB
    c.or
    cK
    c.le
    vq
    vp
    cvlexch.b
    cvlexch.l
    cvlexch.j
    cvlexch.a
    iscvlat
    simprbi
    @18
    @21
    cP
    @9
    c.le
    wbr
    #
    wn
    #
    cP
    @13
    c.le
    wbr
    #
    wa
    #
    @12
    @9
    cP
    c.or
    co
    #
    c.le
    wbr
    #
    wi
    @23
    cP
    @9
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    wa
    #
    cQ
    @26
    c.le
    wbr
    #
    wi
    vp
    vq
    vx
    cP
    cQ
    cX
    cA
    cA
    cB
    @8
    cP
    wceq
    #
    @15
    @25
    @17
    @27
    @32
    @11
    @23
    @14
    @24
    @32
    @10
    @22
    @8
    cP
    @9
    c.le
    breq1
    notbid
    @8
    cP
    @13
    c.le
    breq1
    anbi12d
    @32
    @16
    @26
    @12
    c.le
    @8
    cP
    @9
    c.or
    oveq2
    breq2d
    imbi12d
    @12
    cQ
    wceq
    #
    @25
    @30
    @27
    @31
    @33
    @24
    @29
    @23
    @33
    @13
    @28
    cP
    c.le
    @12
    cQ
    @9
    c.or
    oveq2
    breq2d
    anbi2d
    @12
    cQ
    @26
    c.le
    breq1
    imbi12d
    @9
    cX
    wceq
    #
    @30
    @20
    @31
    @7
    @34
    @23
    @3
    @29
    @5
    @34
    @22
    @2
    @9
    cX
    cP
    c.le
    breq2
    notbid
    @34
    @28
    @4
    cP
    c.le
    @9
    cX
    cQ
    c.or
    oveq1
    breq2d
    anbi12d
    @34
    @26
    @6
    cQ
    c.le
    @9
    cX
    cP
    c.or
    oveq1
    breq2d
    imbi12d
    rspc3v
    mpan9
    exp4b
    3imp
end
