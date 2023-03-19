include "cvv.mm"
include "wcel.mm"
include "cxp.mm"
include "crest.mm"
include "co.mm"
include "cuss.mm"
include "cfv.mm"
include "wceq.mm"
include "cunif.mm"
include "cbs.mm"
include "cv.mm"
include "fveq2.mm"
include "sqxpeqd.mm"
include "oveq12d.mm"
include "df-uss.mm"
include "ovex.mm"
include "fvmpt.mm"
include "xpeq12i.mm"
include "oveq12i.mm"
include "syl6reqr.mm"
include "wn.mm"
include "c0.mm"
include "0rest.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "oveq1d.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem ussval
  let cB: class B
  let cU: class U
  let cW: class W
  let vw: setvar w
  assume ussval.1: |- B = ( Base ` W )
  assume ussval.2: |- U = ( UnifSet ` W )


  assert |- ( U |`t ( B X. B ) ) = ( UnifSt ` W )

  proof
    cW
    cvv
    wcel
    #
    cU
    cB
    cB
    cxp
    #
    crest
    co
    #
    cW
    cuss
    cfv
    #
    wceq
    @0
    @3
    cW
    cunif
    cfv
    #
    cW
    cbs
    cfv
    #
    @5
    cxp
    #
    crest
    co
    #
    @2
    vw
    cW
    vw
    cv
    #
    cunif
    cfv
    #
    @8
    cbs
    cfv
    #
    @10
    cxp
    #
    crest
    co
    @7
    cvv
    cuss
    @8
    cW
    wceq
    #
    @9
    @4
    @11
    @6
    crest
    @8
    cW
    cunif
    fveq2
    @12
    @10
    @5
    @8
    cW
    cbs
    fveq2
    sqxpeqd
    oveq12d
    vw
    df-uss
    @4
    @6
    crest
    ovex
    fvmpt
    cU
    @4
    @1
    @6
    crest
    ussval.2
    cB
    @5
    cB
    @5
    ussval.1
    ussval.1
    xpeq12i
    oveq12i
    syl6reqr
    @0
    wn
    #
    c0
    @1
    crest
    co
    c0
    @2
    @3
    @1
    0rest
    @13
    cU
    c0
    @1
    crest
    @13
    cU
    @4
    c0
    ussval.2
    cW
    cunif
    fvprc
    syl5eq
    oveq1d
    cW
    cuss
    fvprc
    3eqtr4a
    pm2.61i
end
