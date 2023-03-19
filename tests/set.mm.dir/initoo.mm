include "ccat.mm"
include "wcel.mm"
include "cinito.mm"
include "cfv.mm"
include "cbs.mm"
include "wa.mm"
include "cv.mm"
include "chom.mm"
include "co.mm"
include "weu.mm"
include "wral.mm"
include "eqid.mm"
include "id.mm"
include "isinitoi.mm"
include "simpld.mm"
include "ex.mm"

theorem initoo
  let cC: class C
  let cO: class O
  let vb: setvar b
  let vh: setvar h


  assert |- ( C e. Cat -> ( O e. ( InitO ` C ) -> O e. ( Base ` C ) ) )

  proof
    cC
    ccat
    wcel
    #
    cO
    cC
    cinito
    cfv
    wcel
    #
    cO
    cC
    cbs
    cfv
    #
    wcel
    #
    @0
    @1
    wa
    @3
    vh
    cv
    cO
    vb
    cv
    cC
    chom
    cfv
    #
    co
    wcel
    vh
    weu
    vb
    @2
    wral
    @0
    @2
    cC
    vh
    @4
    cO
    vb
    @2
    eqid
    @4
    eqid
    @0
    id
    isinitoi
    simpld
    ex
end
