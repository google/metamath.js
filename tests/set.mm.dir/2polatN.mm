include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cfv.mm"
include "coc.mm"
include "cpmap.mm"
include "col.mm"
include "wceq.mm"
include "hlol.mm"
include "eqid.mm"
include "polatN.mm"
include "sylan.mm"
include "fveq2d.mm"
include "cbs.mm"
include "cops.mm"
include "hlop.mm"
include "atbase.mm"
include "opoccl.mm"
include "syl2an.mm"
include "polpmapN.mm"
include "syldan.mm"
include "opococ.mm"
include "pmapat.mm"
include "eqtrd.mm"

theorem 2polatN
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cK: class K
  assume 2polat.a: |- A = ( Atoms ` K )
  assume 2polat.p: |- P = ( _|_P ` K )


  assert |- ( ( K e. HL /\ Q e. A ) -> ( P ` ( P ` { Q } ) ) = { Q } )

  proof
    cK
    chlt
    wcel
    #
    cQ
    cA
    wcel
    #
    wa
    #
    cQ
    csn
    #
    cP
    cfv
    #
    cP
    cfv
    cQ
    cK
    coc
    cfv
    #
    cfv
    #
    cK
    cpmap
    cfv
    #
    cfv
    #
    cP
    cfv
    #
    @3
    @2
    @4
    @8
    cP
    @0
    cK
    col
    wcel
    @1
    @4
    @8
    wceq
    cK
    hlol
    cA
    cP
    cQ
    cK
    @7
    @5
    @5
    eqid
    #
    2polat.a
    @7
    eqid
    #
    2polat.p
    polatN
    sylan
    fveq2d
    @2
    @9
    @6
    @5
    cfv
    #
    @7
    cfv
    #
    @3
    @0
    @1
    @6
    cK
    cbs
    cfv
    #
    wcel
    #
    @9
    @13
    wceq
    @0
    cK
    cops
    wcel
    #
    cQ
    @14
    wcel
    #
    @15
    @1
    cK
    hlop
    #
    cA
    @14
    cQ
    cK
    @14
    eqid
    #
    2polat.a
    atbase
    #
    @14
    cK
    @5
    cQ
    @19
    @10
    opoccl
    syl2an
    @14
    cP
    cK
    @7
    @5
    @6
    @19
    @10
    @11
    2polat.p
    polpmapN
    syldan
    @2
    @13
    cQ
    @7
    cfv
    @3
    @2
    @12
    cQ
    @7
    @0
    @16
    @17
    @12
    cQ
    wceq
    @1
    @18
    @20
    @14
    cK
    @5
    cQ
    @19
    @10
    opococ
    syl2an
    fveq2d
    cA
    cQ
    cK
    @7
    2polat.a
    @11
    pmapat
    eqtrd
    eqtrd
    eqtrd
end
