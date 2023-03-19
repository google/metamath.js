include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "clat.mm"
include "wceq.mm"
include "hllat.mm"
include "3ad2ant1.mm"
include "simp21.mm"
include "atbase.mm"
include "syl.mm"
include "simp22.mm"
include "latjcom.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "latjcl.mm"
include "simp23.mm"
include "latmcom.mm"
include "eqtrd.mm"
include "simp1.mm"
include "3jca.mm"
include "simp31.mm"
include "necomd.mm"
include "simp33.mm"
include "cops.mm"
include "hlop.mm"
include "ople1.mm"
include "syl2anc.mm"
include "simp32.mm"
include "1cvrjat.mm"
include "syl32anc.mm"
include "breqtrrd.mm"
include "wa.mm"
include "cvrat3.mm"
include "imp.mm"
include "syl23anc.mm"
include "eqeltrd.mm"

theorem 1cvrat
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let c.1: class .1.
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cX: class X
  assume 1cvrat.b: |- B = ( Base ` K )
  assume 1cvrat.l: |- .<_ = ( le ` K )
  assume 1cvrat.j: |- .\/ = ( join ` K )
  assume 1cvrat.m: |- ./\ = ( meet ` K )
  assume 1cvrat.u: |- .1. = ( 1. ` K )
  assume 1cvrat.c: |- C = ( <o ` K )
  assume 1cvrat.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ X e. B ) /\ ( P =/= Q /\ X C .1. /\ -. P .<_ X ) ) -> ( ( P .\/ Q ) ./\ X ) e. A )

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
    cX
    cB
    wcel
    #
    w3a
    #
    cP
    cQ
    wne
    #
    cX
    c.1
    cC
    wbr
    #
    cP
    cX
    c.le
    wbr
    wn
    #
    w3a
    #
    w3a
    #
    cP
    cQ
    c.or
    co
    #
    cX
    c.an
    co
    #
    cX
    cQ
    cP
    c.or
    co
    #
    c.an
    co
    #
    cA
    @9
    @11
    @12
    cX
    c.an
    co
    #
    @13
    @9
    @10
    @12
    cX
    c.an
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
    @10
    @12
    wceq
    @0
    @4
    @15
    @8
    cK
    hllat
    3ad2ant1
    #
    @9
    @1
    @16
    @0
    @1
    @2
    @3
    @8
    simp21
    #
    cA
    cB
    cP
    cK
    1cvrat.b
    1cvrat.a
    atbase
    syl
    #
    @9
    @2
    @17
    @0
    @1
    @2
    @3
    @8
    simp22
    #
    cA
    cB
    cQ
    cK
    1cvrat.b
    1cvrat.a
    atbase
    syl
    #
    cB
    c.or
    cK
    cP
    cQ
    1cvrat.b
    1cvrat.j
    latjcom
    syl3anc
    oveq1d
    @9
    @15
    @12
    cB
    wcel
    #
    @3
    @14
    @13
    wceq
    @18
    @9
    @15
    @17
    @16
    @23
    @18
    @22
    @20
    cB
    c.or
    cK
    cQ
    cP
    1cvrat.b
    1cvrat.j
    latjcl
    syl3anc
    @0
    @1
    @2
    @3
    @8
    simp23
    #
    cB
    cK
    c.an
    @12
    cX
    1cvrat.b
    1cvrat.m
    latmcom
    syl3anc
    eqtrd
    @9
    @0
    @3
    @2
    @1
    w3a
    #
    cQ
    cP
    wne
    #
    @7
    cQ
    cX
    cP
    c.or
    co
    #
    c.le
    wbr
    #
    @13
    cA
    wcel
    #
    @0
    @4
    @8
    simp1
    #
    @9
    @3
    @2
    @1
    @24
    @21
    @19
    3jca
    @9
    cP
    cQ
    @0
    @4
    @5
    @6
    @7
    simp31
    necomd
    @0
    @4
    @5
    @6
    @7
    simp33
    #
    @9
    cQ
    c.1
    @27
    c.le
    @9
    cK
    cops
    wcel
    #
    @17
    cQ
    c.1
    c.le
    wbr
    @0
    @4
    @32
    @8
    cK
    hlop
    3ad2ant1
    @22
    cB
    c.1
    cK
    c.le
    cQ
    1cvrat.b
    1cvrat.l
    1cvrat.u
    ople1
    syl2anc
    @9
    @0
    @3
    @1
    @6
    @7
    @27
    c.1
    wceq
    @30
    @24
    @19
    @0
    @4
    @5
    @6
    @7
    simp32
    @31
    cA
    cB
    cC
    cP
    c.1
    c.or
    cK
    c.le
    cX
    1cvrat.b
    1cvrat.l
    1cvrat.j
    1cvrat.u
    1cvrat.c
    1cvrat.a
    1cvrjat
    syl32anc
    breqtrrd
    @0
    @25
    wa
    @26
    @7
    @28
    w3a
    @29
    cA
    cB
    cQ
    cP
    c.or
    cK
    c.le
    c.an
    cX
    1cvrat.b
    1cvrat.l
    1cvrat.j
    1cvrat.m
    1cvrat.a
    cvrat3
    imp
    syl23anc
    eqeltrd
end
