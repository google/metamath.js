include "cmgm.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "wf.mm"
include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "cmgmhm.mm"
include "id.mm"
include "ancri.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1of.mm"
include "mp1i.mm"
include "eqid.mm"
include "mgmcl.mm"
include "3expb.mm"
include "fvresi.mm"
include "syl.mm"
include "oveqan12d.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "ralrimivva.mm"
include "jca.mm"
include "ismgmhm.mm"
include "sylanbrc.mm"

theorem idmgmhm
  let cB: class B
  let cM: class M
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  let vx: setvar x
  assume idmgmhm.b: |- B = ( Base ` M )


  assert |- ( M e. Mgm -> ( _I |` B ) e. ( M MgmHom M ) )

  proof
    cM
    cmgm
    wcel
    #
    @0
    @0
    wa
    cB
    cB
    cid
    cB
    cres
    #
    wf
    #
    va
    cv
    #
    vb
    cv
    #
    cM
    cplusg
    cfv
    #
    co
    #
    @1
    cfv
    #
    @3
    @1
    cfv
    #
    @4
    @1
    cfv
    #
    @5
    co
    #
    wceq
    #
    vb
    cB
    wral
    va
    cB
    wral
    #
    wa
    @1
    cM
    cM
    cmgmhm
    co
    wcel
    @0
    @0
    @0
    id
    ancri
    @0
    @2
    @12
    cB
    cB
    @1
    wf1o
    @2
    @0
    cB
    f1oi
    cB
    cB
    @1
    f1of
    mp1i
    @0
    @11
    va
    vb
    cB
    cB
    @0
    @3
    cB
    wcel
    #
    @4
    cB
    wcel
    #
    wa
    #
    wa
    #
    @7
    @6
    @10
    @16
    @6
    cB
    wcel
    #
    @7
    @6
    wceq
    @0
    @13
    @14
    @17
    cB
    cM
    @3
    @4
    @5
    idmgmhm.b
    @5
    eqid
    #
    mgmcl
    3expb
    cB
    @6
    fvresi
    syl
    @15
    @10
    @6
    wceq
    @0
    @13
    @14
    @8
    @3
    @9
    @4
    @5
    cB
    @3
    fvresi
    cB
    @4
    fvresi
    oveqan12d
    adantl
    eqtr4d
    ralrimivva
    jca
    va
    vb
    cB
    cB
    @5
    @5
    cM
    cM
    @1
    idmgmhm.b
    idmgmhm.b
    @18
    @18
    ismgmhm
    sylanbrc
end
