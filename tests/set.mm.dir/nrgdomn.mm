include "cnrg.mm"
include "wcel.mm"
include "cdomn.mm"
include "cnzr.mm"
include "domnnzr.mm"
include "wa.mm"
include "cabv.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "simpr.mm"
include "cnm.mm"
include "eqid.mm"
include "nrgabv.mm"
include "ne0i.mm"
include "syl.mm"
include "adantr.mm"
include "abvn0b.mm"
include "sylanbrc.mm"
include "ex.mm"
include "impbid2.mm"

theorem nrgdomn
  let cR: class R


  assert |- ( R e. NrmRing -> ( R e. Domn <-> R e. NzRing ) )

  proof
    cR
    cnrg
    wcel
    #
    cR
    cdomn
    wcel
    #
    cR
    cnzr
    wcel
    #
    cR
    domnnzr
    @0
    @2
    @1
    @0
    @2
    wa
    @2
    cR
    cabv
    cfv
    #
    c0
    wne
    #
    @1
    @0
    @2
    simpr
    @0
    @4
    @2
    @0
    cR
    cnm
    cfv
    #
    @3
    wcel
    @4
    @3
    cR
    @5
    @5
    eqid
    @3
    eqid
    #
    nrgabv
    @3
    @5
    ne0i
    syl
    adantr
    @3
    cR
    @6
    abvn0b
    sylanbrc
    ex
    impbid2
end
