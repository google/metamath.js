include "cngp.mm"
include "wcel.mm"
include "cid.mm"
include "cres.mm"
include "cnghm.mm"
include "co.mm"
include "cnmo.mm"
include "cfv.mm"
include "cr.mm"
include "c0g.mm"
include "csn.mm"
include "wpss.mm"
include "wceq.mm"
include "wa.mm"
include "c1.mm"
include "eqid.mm"
include "nmoid.mm"
include "1re.mm"
include "syl6eqel.mm"
include "cc0.mm"
include "cxp.mm"
include "cv.mm"
include "cmpt.mm"
include "eleq2.mm"
include "biimpar.mm"
include "elsni.mm"
include "syl.mm"
include "mpteq2dva.mm"
include "mptresid.mm"
include "eqcomi.mm"
include "fconstmpt.mm"
include "3eqtr4g.mm"
include "fveq2d.mm"
include "nmo0.mm"
include "anidms.mm"
include "sylan9eqr.mm"
include "0re.mm"
include "wss.mm"
include "wo.mm"
include "cgrp.mm"
include "ngpgrp.mm"
include "grpidcl.mm"
include "snssd.mm"
include "sspss.mm"
include "sylib.mm"
include "mpjaodan.mm"
include "cghm.mm"
include "wb.mm"
include "id.mm"
include "idghm.mm"
include "isnghm2.mm"
include "mpd3an23.mm"
include "mpbird.mm"

theorem idnghm
  let cS: class S
  let cV: class V
  let vx: setvar x
  assume idnghm.2: |- V = ( Base ` S )


  assert |- ( S e. NrmGrp -> ( _I |` V ) e. ( S NGHom S ) )

  proof
    cS
    cngp
    wcel
    #
    cid
    cV
    cres
    #
    cS
    cS
    cnghm
    co
    wcel
    #
    @1
    cS
    cS
    cnmo
    co
    #
    cfv
    #
    cr
    wcel
    #
    @0
    cS
    c0g
    cfv
    #
    csn
    #
    cV
    wpss
    #
    @5
    @7
    cV
    wceq
    #
    @0
    @8
    wa
    @4
    c1
    cr
    cS
    @3
    cV
    @6
    @3
    eqid
    #
    idnghm.2
    @6
    eqid
    #
    nmoid
    1re
    syl6eqel
    @0
    @9
    wa
    @4
    cc0
    cr
    @9
    @0
    @4
    cV
    @7
    cxp
    #
    @3
    cfv
    #
    cc0
    @9
    @1
    @12
    @3
    @9
    vx
    cV
    vx
    cv
    #
    cmpt
    #
    vx
    cV
    @6
    cmpt
    @1
    @12
    @9
    vx
    cV
    @14
    @6
    @9
    @14
    cV
    wcel
    #
    wa
    @14
    @7
    wcel
    #
    @14
    @6
    wceq
    @9
    @17
    @16
    @7
    cV
    @14
    eleq2
    biimpar
    @14
    @6
    elsni
    syl
    mpteq2dva
    @15
    @1
    vx
    cV
    mptresid
    eqcomi
    vx
    cV
    @6
    fconstmpt
    3eqtr4g
    fveq2d
    @0
    @13
    cc0
    wceq
    cS
    cS
    @3
    cV
    @6
    @10
    idnghm.2
    @11
    nmo0
    anidms
    sylan9eqr
    0re
    syl6eqel
    @0
    @7
    cV
    wss
    @8
    @9
    wo
    @0
    @6
    cV
    @0
    cS
    cgrp
    wcel
    #
    @6
    cV
    wcel
    cS
    ngpgrp
    #
    cV
    cS
    @6
    idnghm.2
    @11
    grpidcl
    syl
    snssd
    @7
    cV
    sspss
    sylib
    mpjaodan
    @0
    @0
    @1
    cS
    cS
    cghm
    co
    wcel
    #
    @2
    @5
    wb
    @0
    id
    @0
    @18
    @20
    @19
    cV
    cS
    idnghm.2
    idghm
    syl
    cS
    cS
    @1
    @3
    @10
    isnghm2
    mpd3an23
    mpbird
end
