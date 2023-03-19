include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "cple.mm"
include "cfv.mm"
include "cbs.mm"
include "wa.mm"
include "simpl1.mm"
include "simpl21.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "clat.mm"
include "hllat.mm"
include "simpl22.mm"
include "simpl23.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "3jca.mm"
include "cvrle.mm"
include "sylancom.mm"
include "ex.mm"
include "hlatexch2.mm"
include "simpl3.mm"
include "simpr.mm"
include "atcvrj2.mm"
include "syl132anc.mm"
include "3syld.mm"

theorem atexchcvrN
  let cA: class A
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  assume atexchcvr.j: |- .\/ = ( join ` K )
  assume atexchcvr.a: |- A = ( Atoms ` K )
  assume atexchcvr.c: |- C = ( <o ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) /\ P =/= R ) -> ( P C ( Q .\/ R ) -> Q C ( P .\/ R ) ) )

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
    cR
    cA
    wcel
    #
    w3a
    #
    cP
    cR
    wne
    #
    w3a
    #
    cP
    cQ
    cR
    c.or
    co
    #
    cC
    wbr
    #
    cP
    @7
    cK
    cple
    cfv
    #
    wbr
    #
    cQ
    cP
    cR
    c.or
    co
    #
    @9
    wbr
    #
    cQ
    @11
    cC
    wbr
    #
    @6
    @8
    @10
    @6
    @8
    @0
    cP
    cK
    cbs
    cfv
    #
    wcel
    #
    @7
    @14
    wcel
    #
    w3a
    @10
    @6
    @8
    wa
    #
    @0
    @15
    @16
    @0
    @4
    @5
    @8
    simpl1
    #
    @17
    @1
    @15
    @1
    @2
    @3
    @0
    @5
    @8
    simpl21
    cA
    @14
    cP
    cK
    @14
    eqid
    #
    atexchcvr.a
    atbase
    syl
    @17
    cK
    clat
    wcel
    #
    cQ
    @14
    wcel
    #
    cR
    @14
    wcel
    #
    @16
    @17
    @0
    @20
    @18
    cK
    hllat
    syl
    @17
    @2
    @21
    @1
    @2
    @3
    @0
    @5
    @8
    simpl22
    cA
    @14
    cQ
    cK
    @19
    atexchcvr.a
    atbase
    syl
    @17
    @3
    @22
    @1
    @2
    @3
    @0
    @5
    @8
    simpl23
    cA
    @14
    cR
    cK
    @19
    atexchcvr.a
    atbase
    syl
    @14
    c.or
    cK
    cQ
    cR
    @19
    atexchcvr.j
    latjcl
    syl3anc
    3jca
    chlt
    @14
    cC
    cK
    @9
    cP
    @7
    @19
    @9
    eqid
    #
    atexchcvr.c
    cvrle
    sylancom
    ex
    cA
    cP
    cQ
    cR
    c.or
    cK
    @9
    @23
    atexchcvr.j
    atexchcvr.a
    hlatexch2
    @6
    @12
    @13
    @6
    @12
    wa
    @0
    @2
    @1
    @3
    @5
    @12
    @13
    @0
    @4
    @5
    @12
    simpl1
    @1
    @2
    @3
    @0
    @5
    @12
    simpl22
    @1
    @2
    @3
    @0
    @5
    @12
    simpl21
    @1
    @2
    @3
    @0
    @5
    @12
    simpl23
    @0
    @4
    @5
    @12
    simpl3
    @6
    @12
    simpr
    cA
    cC
    cQ
    cP
    cR
    c.or
    cK
    @9
    @23
    atexchcvr.j
    atexchcvr.c
    atexchcvr.a
    atcvrj2
    syl132anc
    ex
    3syld
end
