include "chlt.mm"
include "wcel.mm"
include "cfv.mm"
include "w3a.mm"
include "wne.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "simp11.mm"
include "simp12.mm"
include "jca.mm"
include "simp13.mm"
include "isline3.mm"
include "biimpd.mm"
include "sylc.mm"
include "simp3r.mm"
include "simp111.mm"
include "simp121.mm"
include "simp122.mm"
include "simp2.mm"
include "3jca.mm"
include "simp123.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "simp21.mm"
include "atbase.mm"
include "simp22.mm"
include "simp3.mm"
include "latjle12.mm"
include "3ad2ant1.mm"
include "breqtrd.mm"
include "wb.mm"
include "simpl1.mm"
include "simpl2l.mm"
include "simpl2r.mm"
include "simpr.mm"
include "simpl3.mm"
include "ps-1.mm"
include "syl131anc.mm"
include "eqtr4d.mm"
include "3exp.mm"
include "rexlimdvv.mm"
include "mpd.mm"

theorem lneq2at
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cM: class M
  let cN: class N
  let cX: class X
  let vr: setvar r
  let vs: setvar s
  assume lneq2at.b: |- B = ( Base ` K )
  assume lneq2at.l: |- .<_ = ( le ` K )
  assume lneq2at.j: |- .\/ = ( join ` K )
  assume lneq2at.a: |- A = ( Atoms ` K )
  assume lneq2at.n: |- N = ( Lines ` K )
  assume lneq2at.m: |- M = ( pmap ` K )


  assert |- ( ( ( K e. HL /\ X e. B /\ ( M ` X ) e. N ) /\ ( P e. A /\ Q e. A /\ P =/= Q ) /\ ( P .<_ X /\ Q .<_ X ) ) -> X = ( P .\/ Q ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    cX
    cM
    cfv
    cN
    wcel
    #
    w3a
    #
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    cP
    cQ
    wne
    #
    w3a
    #
    cP
    cX
    c.le
    wbr
    cQ
    cX
    c.le
    wbr
    wa
    #
    w3a
    #
    vr
    cv
    #
    vs
    cv
    #
    wne
    #
    cX
    @10
    @11
    c.or
    co
    #
    wceq
    #
    wa
    #
    vs
    cA
    wrex
    vr
    cA
    wrex
    #
    cX
    cP
    cQ
    c.or
    co
    #
    wceq
    #
    @9
    @0
    @1
    wa
    #
    @2
    @16
    @9
    @0
    @1
    @0
    @1
    @2
    @7
    @8
    simp11
    #
    @0
    @1
    @2
    @7
    @8
    simp12
    #
    jca
    @0
    @1
    @2
    @7
    @8
    simp13
    @19
    @2
    @16
    cA
    cB
    c.or
    cK
    cM
    cN
    cX
    vs
    vr
    lneq2at.b
    lneq2at.j
    lneq2at.a
    lneq2at.n
    lneq2at.m
    isline3
    biimpd
    sylc
    @9
    @15
    @18
    vr
    vs
    cA
    cA
    @9
    @10
    cA
    wcel
    @11
    cA
    wcel
    wa
    #
    @15
    @18
    @9
    @22
    @15
    w3a
    #
    cX
    @13
    @17
    @9
    @22
    @12
    @14
    simp3r
    #
    @23
    @0
    @4
    @5
    wa
    #
    @22
    w3a
    #
    @6
    wa
    #
    @17
    @13
    c.le
    wbr
    #
    @17
    @13
    wceq
    #
    @23
    @26
    @6
    @23
    @0
    @25
    @22
    @0
    @1
    @2
    @7
    @8
    @22
    @15
    simp111
    @23
    @4
    @5
    @4
    @5
    @6
    @3
    @8
    @22
    @15
    simp121
    @4
    @5
    @6
    @3
    @8
    @22
    @15
    simp122
    jca
    @9
    @22
    @15
    simp2
    3jca
    @4
    @5
    @6
    @3
    @8
    @22
    @15
    simp123
    jca
    @23
    @17
    cX
    @13
    c.le
    @9
    @22
    @17
    cX
    c.le
    wbr
    #
    @15
    @9
    cK
    clat
    wcel
    #
    cP
    cB
    wcel
    #
    cQ
    cB
    wcel
    #
    @1
    w3a
    #
    wa
    #
    @8
    @30
    @9
    @31
    @34
    @9
    @0
    @31
    @20
    cK
    hllat
    syl
    @9
    @32
    @33
    @1
    @9
    @4
    @32
    @3
    @4
    @5
    @6
    @8
    simp21
    cA
    cB
    cP
    cK
    lneq2at.b
    lneq2at.a
    atbase
    syl
    @9
    @5
    @33
    @3
    @4
    @5
    @6
    @8
    simp22
    cA
    cB
    cQ
    cK
    lneq2at.b
    lneq2at.a
    atbase
    syl
    @21
    3jca
    jca
    @3
    @7
    @8
    simp3
    @35
    @8
    @30
    cB
    c.or
    cK
    c.le
    cP
    cQ
    cX
    lneq2at.b
    lneq2at.l
    lneq2at.j
    latjle12
    biimpd
    sylc
    3ad2ant1
    @24
    breqtrd
    @27
    @28
    @29
    @27
    @0
    @4
    @5
    @6
    @22
    @28
    @29
    wb
    @0
    @25
    @22
    @6
    simpl1
    @4
    @5
    @0
    @22
    @6
    simpl2l
    @4
    @5
    @0
    @22
    @6
    simpl2r
    @26
    @6
    simpr
    @0
    @25
    @22
    @6
    simpl3
    cA
    cP
    cQ
    @10
    @11
    c.or
    cK
    c.le
    lneq2at.l
    lneq2at.j
    lneq2at.a
    ps-1
    syl131anc
    biimpd
    sylc
    eqtr4d
    3exp
    rexlimdvv
    mpd
end
