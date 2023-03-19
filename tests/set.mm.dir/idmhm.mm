include "cmnd.mm"
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
include "c0g.mm"
include "w3a.mm"
include "cmhm.mm"
include "id.mm"
include "ancri.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1of.mm"
include "mp1i.mm"
include "eqid.mm"
include "mndcl.mm"
include "3expb.mm"
include "fvresi.mm"
include "syl.mm"
include "oveqan12d.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "ralrimivva.mm"
include "mndidcl.mm"
include "3jca.mm"
include "ismhm.mm"
include "sylanbrc.mm"

theorem idmhm
  let cB: class B
  let cM: class M
  let va: setvar a
  let vb: setvar b
  assume idmhm.b: |- B = ( Base ` M )


  assert |- ( M e. Mnd -> ( _I |` B ) e. ( M MndHom M ) )

  proof
    cM
    cmnd
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
    cM
    c0g
    cfv
    #
    @1
    cfv
    @13
    wceq
    #
    w3a
    @1
    cM
    cM
    cmhm
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
    @14
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
    @18
    @6
    cB
    wcel
    #
    @7
    @6
    wceq
    @0
    @15
    @16
    @19
    cB
    @5
    cM
    @3
    @4
    idmhm.b
    @5
    eqid
    #
    mndcl
    3expb
    cB
    @6
    fvresi
    syl
    @17
    @10
    @6
    wceq
    @0
    @15
    @16
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
    @0
    @13
    cB
    wcel
    @14
    cB
    cM
    @13
    idmhm.b
    @13
    eqid
    #
    mndidcl
    cB
    @13
    fvresi
    syl
    3jca
    va
    vb
    cB
    cB
    @5
    @5
    cM
    cM
    @1
    @13
    @13
    idmhm.b
    idmhm.b
    @20
    @20
    @21
    @21
    ismhm
    sylanbrc
end
