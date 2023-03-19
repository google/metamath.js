include "cxp.mm"
include "cuni.mm"
include "wceq.mm"
include "crest.mm"
include "co.mm"
include "cuss.mm"
include "cfv.mm"
include "oveq2.mm"
include "cvv.mm"
include "wcel.mm"
include "id.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "xpex.mm"
include "syl6eqelr.mm"
include "uniexb.mm"
include "sylibr.mm"
include "eqid.mm"
include "restid.mm"
include "syl.mm"
include "eqtr2d.mm"
include "ussval.mm"
include "syl6eq.mm"

theorem ussid
  let cB: class B
  let cU: class U
  let cW: class W
  let vw: setvar w
  assume ussval.1: |- B = ( Base ` W )
  assume ussval.2: |- U = ( UnifSet ` W )


  assert |- ( ( B X. B ) = U. U -> U = ( UnifSt ` W ) )

  proof
    cB
    cB
    cxp
    #
    cU
    cuni
    #
    wceq
    #
    cU
    cU
    @0
    crest
    co
    #
    cW
    cuss
    cfv
    @2
    @3
    cU
    @1
    crest
    co
    #
    cU
    @0
    @1
    cU
    crest
    oveq2
    @2
    cU
    cvv
    wcel
    #
    @4
    cU
    wceq
    @2
    @1
    cvv
    wcel
    @5
    @2
    @1
    @0
    cvv
    @2
    id
    cB
    cB
    cB
    cW
    cbs
    cfv
    cvv
    ussval.1
    cW
    cbs
    fvex
    eqeltri
    #
    @6
    xpex
    syl6eqelr
    cU
    uniexb
    sylibr
    cU
    cvv
    @1
    @1
    eqid
    restid
    syl
    eqtr2d
    cB
    cU
    cW
    ussval.1
    ussval.2
    ussval
    syl6eq
end
