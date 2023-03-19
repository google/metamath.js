include "csubrg.mm"
include "cfv.mm"
include "wcel.mm"
include "cress.mm"
include "co.mm"
include "cur.mm"
include "cod.mm"
include "cchr.mm"
include "csubg.mm"
include "wceq.mm"
include "subrgsubg.mm"
include "eqid.mm"
include "subrg1cl.mm"
include "subgod.mm"
include "syl2anc.mm"
include "subrg1.mm"
include "fveq2d.mm"
include "eqtr2d.mm"
include "chrval.mm"
include "3eqtr3g.mm"

theorem subrgchr
  let cA: class A
  let cR: class R


  assert |- ( A e. ( SubRing ` R ) -> ( chr ` ( R |`s A ) ) = ( chr ` R ) )

  proof
    cA
    cR
    csubrg
    cfv
    wcel
    #
    cR
    cA
    cress
    co
    #
    cur
    cfv
    #
    @1
    cod
    cfv
    #
    cfv
    #
    cR
    cur
    cfv
    #
    cR
    cod
    cfv
    #
    cfv
    #
    @1
    cchr
    cfv
    #
    cR
    cchr
    cfv
    #
    @0
    @7
    @5
    @3
    cfv
    #
    @4
    @0
    cA
    cR
    csubg
    cfv
    wcel
    @5
    cA
    wcel
    @7
    @10
    wceq
    cA
    cR
    subrgsubg
    cA
    cR
    @5
    @5
    eqid
    #
    subrg1cl
    @5
    @3
    cR
    @1
    @6
    cA
    @1
    eqid
    #
    @6
    eqid
    #
    @3
    eqid
    #
    subgod
    syl2anc
    @0
    @5
    @2
    @3
    cA
    cR
    @1
    @5
    @12
    @11
    subrg1
    fveq2d
    eqtr2d
    @8
    @1
    @2
    @3
    @14
    @2
    eqid
    @8
    eqid
    chrval
    @9
    cR
    @5
    @6
    @13
    @11
    @9
    eqid
    chrval
    3eqtr3g
end
