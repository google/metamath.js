include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wceq.mm"
include "wne.mm"
include "wa.mm"
include "wn.mm"
include "atcvr1.mm"
include "atcvr0.mm"
include "3adant3.mm"
include "biantrurd.mm"
include "bitrd.mm"
include "cbs.mm"
include "cfv.mm"
include "wi.mm"
include "simp1.mm"
include "cops.mm"
include "hlop.mm"
include "3ad2ant1.mm"
include "eqid.mm"
include "op0cl.mm"
include "syl.mm"
include "atbase.mm"
include "3ad2ant2.mm"
include "hlatjcl.mm"
include "cvrntr.mm"
include "syl13anc.mm"
include "sylbid.mm"
include "necon4ad.mm"
include "hlatjidm.mm"
include "breqtrrd.mm"
include "oveq2.mm"
include "breq2d.mm"
include "syl5ibcom.mm"
include "impbid.mm"

theorem atcvr0eq
  let cA: class A
  let cC: class C
  let cP: class P
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  let c.0: class .0.
  assume atcvr0eq.j: |- .\/ = ( join ` K )
  assume atcvr0eq.z: |- .0. = ( 0. ` K )
  assume atcvr0eq.c: |- C = ( <o ` K )
  assume atcvr0eq.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ P e. A /\ Q e. A ) -> ( .0. C ( P .\/ Q ) <-> P = Q ) )

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
    c.0
    cP
    cQ
    c.or
    co
    #
    cC
    wbr
    #
    cP
    cQ
    wceq
    #
    @3
    @5
    cP
    cQ
    @3
    cP
    cQ
    wne
    #
    c.0
    cP
    cC
    wbr
    #
    cP
    @4
    cC
    wbr
    #
    wa
    #
    @5
    wn
    #
    @3
    @7
    @9
    @10
    cA
    cC
    cP
    cQ
    c.or
    cK
    atcvr0eq.j
    atcvr0eq.c
    atcvr0eq.a
    atcvr1
    @3
    @8
    @9
    @0
    @1
    @8
    @2
    cA
    cC
    chlt
    cP
    cK
    c.0
    atcvr0eq.z
    atcvr0eq.c
    atcvr0eq.a
    atcvr0
    3adant3
    #
    biantrurd
    bitrd
    @3
    @0
    c.0
    cK
    cbs
    cfv
    #
    wcel
    #
    cP
    @13
    wcel
    #
    @4
    @13
    wcel
    @10
    @11
    wi
    @0
    @1
    @2
    simp1
    @3
    cK
    cops
    wcel
    #
    @14
    @0
    @1
    @16
    @2
    cK
    hlop
    3ad2ant1
    @13
    cK
    c.0
    @13
    eqid
    #
    atcvr0eq.z
    op0cl
    syl
    @1
    @0
    @15
    @2
    cA
    @13
    cP
    cK
    @17
    atcvr0eq.a
    atbase
    3ad2ant2
    cA
    @13
    c.or
    cK
    cP
    cQ
    @17
    atcvr0eq.j
    atcvr0eq.a
    hlatjcl
    chlt
    @13
    cC
    cK
    c.0
    cP
    @4
    @17
    atcvr0eq.c
    cvrntr
    syl13anc
    sylbid
    necon4ad
    @3
    c.0
    cP
    cP
    c.or
    co
    #
    cC
    wbr
    @6
    @5
    @3
    c.0
    cP
    @18
    cC
    @12
    @0
    @1
    @18
    cP
    wceq
    @2
    cA
    c.or
    cK
    cP
    atcvr0eq.j
    atcvr0eq.a
    hlatjidm
    3adant3
    breqtrrd
    @6
    @18
    @4
    c.0
    cC
    cP
    cQ
    cP
    c.or
    oveq2
    breq2d
    syl5ibcom
    impbid
end
