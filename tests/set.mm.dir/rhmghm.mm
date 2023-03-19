include "crh.mm"
include "co.mm"
include "wcel.mm"
include "cghm.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmhm.mm"
include "crg.mm"
include "wa.mm"
include "eqid.mm"
include "isrhm.mm"
include "simprbi.mm"
include "simpld.mm"

theorem rhmghm
  let cR: class R
  let cS: class S
  let cF: class F


  assert |- ( F e. ( R RingHom S ) -> F e. ( R GrpHom S ) )

  proof
    cF
    cR
    cS
    crh
    co
    wcel
    #
    cF
    cR
    cS
    cghm
    co
    wcel
    #
    cF
    cR
    cmgp
    cfv
    #
    cS
    cmgp
    cfv
    #
    cmhm
    co
    wcel
    #
    @0
    cR
    crg
    wcel
    cS
    crg
    wcel
    wa
    @1
    @4
    wa
    cR
    cS
    cF
    @2
    @3
    @2
    eqid
    @3
    eqid
    isrhm
    simprbi
    simpld
end
