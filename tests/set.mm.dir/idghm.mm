include "cgrp.mm"
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
include "cghm.mm"
include "id.mm"
include "ancli.mm"
include "eqid.mm"
include "grpcl.mm"
include "3expb.mm"
include "fvresi.mm"
include "syl.mm"
include "oveqan12d.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "ralrimivva.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1of.mm"
include "ax-mp.mm"
include "jctil.mm"
include "isghm.mm"
include "sylanbrc.mm"

theorem idghm
  let cB: class B
  let cG: class G
  let va: setvar a
  let vb: setvar b
  assume idghm.b: |- B = ( Base ` G )


  assert |- ( G e. Grp -> ( _I |` B ) e. ( G GrpHom G ) )

  proof
    cG
    cgrp
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
    cG
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
    cG
    cG
    cghm
    co
    wcel
    @0
    @0
    @0
    id
    ancli
    @0
    @12
    @2
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
    @5
    cG
    @3
    @4
    idghm.b
    @5
    eqid
    #
    grpcl
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
    cB
    cB
    @1
    wf1o
    @2
    cB
    f1oi
    cB
    cB
    @1
    f1of
    ax-mp
    jctil
    vb
    va
    @5
    @5
    cG
    cG
    @1
    cB
    cB
    idghm.b
    idghm.b
    @18
    @18
    isghm
    sylanbrc
end
