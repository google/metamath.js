include "csn.mm"
include "cxp.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "csupp.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "eqidd.mm"
include "wfn.mm"
include "wb.mm"
include "fnconstg.mm"
include "adantl.mm"
include "wne.mm"
include "snnzg.mm"
include "simpl.mm"
include "xpexcnv.mm"
include "syl2anc.mm"
include "simpr.mm"
include "fnsuppeq0.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "supp0prc.mm"
include "pm2.61i.mm"

theorem fczsupp0
  let cB: class B
  let cZ: class Z


  assert |- ( ( B X. { Z } ) supp Z ) = (/)

  proof
    cB
    cZ
    csn
    #
    cxp
    #
    cvv
    wcel
    #
    cZ
    cvv
    wcel
    #
    wa
    #
    @1
    cZ
    csupp
    co
    c0
    wceq
    #
    @4
    @5
    @1
    @1
    wceq
    #
    @4
    @1
    eqidd
    @4
    @1
    cB
    wfn
    #
    cB
    cvv
    wcel
    #
    @3
    @5
    @6
    wb
    @3
    @7
    @2
    cB
    cZ
    cvv
    fnconstg
    adantl
    @4
    @0
    c0
    wne
    #
    @2
    @8
    @3
    @9
    @2
    cZ
    cvv
    snnzg
    adantl
    @2
    @3
    simpl
    cB
    @0
    xpexcnv
    syl2anc
    @2
    @3
    simpr
    cB
    @1
    cvv
    cvv
    cZ
    fnsuppeq0
    syl3anc
    mpbird
    @1
    cZ
    supp0prc
    pm2.61i
end
