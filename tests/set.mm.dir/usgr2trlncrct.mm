include "cusgr.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "wa.mm"
include "ctrls.mm"
include "wbr.mm"
include "ccrcts.mm"
include "wn.mm"
include "cc0.mm"
include "wne.mm"
include "usgr2trlncl.mm"
include "imp.mm"
include "wi.mm"
include "crctprop.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "biimpcd.mm"
include "simpl2im.mm"
include "com12.mm"
include "ad2antlr.mm"
include "necon3ad.mm"
include "mpd.mm"
include "ex.mm"

theorem usgr2trlncrct
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( ( G e. USGraph /\ ( # ` F ) = 2 ) -> ( F ( Trails ` G ) P -> -. F ( Circuits ` G ) P ) )

  proof
    cG
    cusgr
    wcel
    #
    cF
    chash
    cfv
    #
    c2
    wceq
    #
    wa
    #
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    #
    cF
    cP
    cG
    ccrcts
    cfv
    wbr
    #
    wn
    #
    @3
    @4
    wa
    #
    cc0
    cP
    cfv
    #
    c2
    cP
    cfv
    #
    wne
    #
    @6
    @3
    @4
    @10
    cP
    cF
    cG
    usgr2trlncl
    imp
    @7
    @5
    @8
    @9
    @2
    @5
    @8
    @9
    wceq
    #
    wi
    @0
    @4
    @5
    @2
    @11
    @5
    @4
    @8
    @1
    cP
    cfv
    #
    wceq
    #
    @2
    @11
    wi
    cP
    cF
    cG
    crctprop
    @2
    @13
    @11
    @2
    @12
    @9
    @8
    @1
    c2
    cP
    fveq2
    eqeq2d
    biimpcd
    simpl2im
    com12
    ad2antlr
    necon3ad
    mpd
    ex
end
