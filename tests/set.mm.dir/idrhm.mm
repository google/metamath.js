include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "cghm.mm"
include "co.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmhm.mm"
include "crh.mm"
include "id.mm"
include "jca.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "idghm.mm"
include "syl.mm"
include "cmnd.mm"
include "eqid.mm"
include "ringmgp.mm"
include "mgpbas.mm"
include "idmhm.mm"
include "isrhm.mm"
include "sylanbrc.mm"

theorem idrhm
  let cB: class B
  let cR: class R
  assume idrhm.b: |- B = ( Base ` R )


  assert |- ( R e. Ring -> ( _I |` B ) e. ( R RingHom R ) )

  proof
    cR
    crg
    wcel
    #
    @0
    @0
    wa
    cid
    cB
    cres
    #
    cR
    cR
    cghm
    co
    wcel
    #
    @1
    cR
    cmgp
    cfv
    #
    @3
    cmhm
    co
    wcel
    #
    wa
    @1
    cR
    cR
    crh
    co
    wcel
    @0
    @0
    @0
    @0
    id
    #
    @5
    jca
    @0
    @2
    @4
    @0
    cR
    cgrp
    wcel
    @2
    cR
    ringgrp
    cB
    cR
    idrhm.b
    idghm
    syl
    @0
    @3
    cmnd
    wcel
    @4
    cR
    @3
    @3
    eqid
    #
    ringmgp
    cB
    @3
    cB
    cR
    @3
    @6
    idrhm.b
    mgpbas
    idmhm
    syl
    jca
    cR
    cR
    @1
    @3
    @3
    @6
    @6
    isrhm
    sylanbrc
end
