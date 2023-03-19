include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cpl1.mm"
include "cfv.mm"
include "cbs.mm"
include "c0g.mm"
include "wne.mm"
include "cn0.mm"
include "simpl.mm"
include "eqid.mm"
include "uc1pcl.mm"
include "adantl.mm"
include "uc1pn0.mm"
include "deg1nn0cl.mm"
include "syl3anc.mm"

theorem uc1pdeg
  let cC: class C
  let cD: class D
  let cR: class R
  let cF: class F
  assume uc1pdeg.d: |- D = ( deg1 ` R )
  assume uc1pdeg.c: |- C = ( Unic1p ` R )


  assert |- ( ( R e. Ring /\ F e. C ) -> ( D ` F ) e. NN0 )

  proof
    cR
    crg
    wcel
    #
    cF
    cC
    wcel
    #
    wa
    @0
    cF
    cR
    cpl1
    cfv
    #
    cbs
    cfv
    #
    wcel
    #
    cF
    @2
    c0g
    cfv
    #
    wne
    #
    cF
    cD
    cfv
    cn0
    wcel
    @0
    @1
    simpl
    @1
    @4
    @0
    @3
    cC
    @2
    cR
    cF
    @2
    eqid
    #
    @3
    eqid
    #
    uc1pdeg.c
    uc1pcl
    adantl
    @1
    @6
    @0
    cC
    @2
    cR
    cF
    @5
    @7
    @5
    eqid
    #
    uc1pdeg.c
    uc1pn0
    adantl
    @3
    cD
    @2
    cR
    cF
    @5
    uc1pdeg.d
    @7
    @9
    @8
    deg1nn0cl
    syl3anc
end
