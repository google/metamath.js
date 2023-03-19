include "crng.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "cghm.mm"
include "co.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmgmhm.mm"
include "crngh.mm"
include "id.mm"
include "jca.mm"
include "cabl.mm"
include "cgrp.mm"
include "rngabl.mm"
include "ablgrp.mm"
include "idghm.mm"
include "3syl.mm"
include "csgrp.mm"
include "cmgm.mm"
include "eqid.mm"
include "rngmgp.mm"
include "sgrpmgm.mm"
include "mgpbas.mm"
include "idmgmhm.mm"
include "isrnghmmul.mm"
include "sylanbrc.mm"

theorem idrnghm
  let cB: class B
  let cR: class R
  let vk: setvar k
  let vx: setvar x
  assume idrnghm.b: |- B = ( Base ` R )


  assert |- ( R e. Rng -> ( _I |` B ) e. ( R RngHomo R ) )

  proof
    cR
    crng
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
    cmgmhm
    co
    wcel
    #
    wa
    @1
    cR
    cR
    crngh
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
    cabl
    wcel
    cR
    cgrp
    wcel
    @2
    cR
    rngabl
    cR
    ablgrp
    cB
    cR
    idrnghm.b
    idghm
    3syl
    @0
    @3
    csgrp
    wcel
    @3
    cmgm
    wcel
    @4
    cR
    @3
    @3
    eqid
    #
    rngmgp
    @3
    sgrpmgm
    cB
    @3
    cB
    cR
    @3
    @6
    idrnghm.b
    mgpbas
    idmgmhm
    3syl
    jca
    cR
    cR
    @1
    @3
    @3
    @6
    @6
    isrnghmmul
    sylanbrc
end
