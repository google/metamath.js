include "crg.mm"
include "wcel.mm"
include "cur.mm"
include "cfv.mm"
include "cod.mm"
include "cn0.mm"
include "eqid.mm"
include "chrval.mm"
include "cbs.mm"
include "ringidcl.mm"
include "odcl.mm"
include "syl.mm"
include "syl5eqelr.mm"

theorem chrcl
  let cC: class C
  let cR: class R
  assume chrcl.c: |- C = ( chr ` R )


  assert |- ( R e. Ring -> C e. NN0 )

  proof
    cR
    crg
    wcel
    #
    cC
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
    cn0
    cC
    cR
    @1
    @2
    @2
    eqid
    #
    @1
    eqid
    #
    chrcl.c
    chrval
    @0
    @1
    cR
    cbs
    cfv
    #
    wcel
    @3
    cn0
    wcel
    @6
    cR
    @1
    @6
    eqid
    #
    @5
    ringidcl
    @1
    cR
    @2
    @6
    @7
    @4
    odcl
    syl
    syl5eqelr
end
