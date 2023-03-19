include "clmod.mm"
include "wcel.mm"
include "cvsca.mm"
include "cfv.mm"
include "cid.mm"
include "cres.mm"
include "csca.mm"
include "cbs.mm"
include "eqid.mm"
include "id.mm"
include "eqidd.mm"
include "cgrp.mm"
include "cghm.mm"
include "co.mm"
include "lmodgrp.mm"
include "idghm.mm"
include "syl.mm"
include "cv.mm"
include "wa.mm"
include "wceq.mm"
include "lmodvscl.mm"
include "3expb.mm"
include "fvresi.mm"
include "ad2antll.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "islmhmd.mm"

theorem idlmhm
  let cB: class B
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  assume idlmhm.b: |- B = ( Base ` M )


  assert |- ( M e. LMod -> ( _I |` B ) e. ( M LMHom M ) )

  proof
    cM
    clmod
    wcel
    #
    vx
    vy
    cM
    cM
    cM
    cvsca
    cfv
    #
    @1
    cid
    cB
    cres
    #
    cM
    csca
    cfv
    #
    @3
    @3
    cbs
    cfv
    #
    cB
    idlmhm.b
    @1
    eqid
    #
    @5
    @3
    eqid
    #
    @6
    @4
    eqid
    #
    @0
    id
    #
    @8
    @0
    @3
    eqidd
    @0
    cM
    cgrp
    wcel
    @2
    cM
    cM
    cghm
    co
    wcel
    cM
    lmodgrp
    cB
    cM
    idlmhm.b
    idghm
    syl
    @0
    vx
    cv
    #
    @4
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    wa
    #
    @9
    @11
    @1
    co
    #
    @2
    cfv
    #
    @14
    @9
    @11
    @2
    cfv
    #
    @1
    co
    @13
    @14
    cB
    wcel
    #
    @15
    @14
    wceq
    @0
    @10
    @12
    @17
    @9
    @1
    @3
    @4
    cB
    cM
    @11
    idlmhm.b
    @6
    @5
    @7
    lmodvscl
    3expb
    cB
    @14
    fvresi
    syl
    @13
    @16
    @11
    @9
    @1
    @12
    @16
    @11
    wceq
    @0
    @10
    cB
    @11
    fvresi
    ad2antll
    oveq2d
    eqtr4d
    islmhmd
end
