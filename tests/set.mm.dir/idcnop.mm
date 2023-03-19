include "cid.mm"
include "chil.mm"
include "cres.mm"
include "ccop.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "cmv.mm"
include "co.mm"
include "cno.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1of.mm"
include "ax-mp.mm"
include "id.mm"
include "wa.mm"
include "fvresi.mm"
include "oveqan12rd.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "biimprd.mm"
include "ralrimiva.mm"
include "weq.mm"
include "breq2.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anr.mm"
include "rgen2.mm"
include "elcnop.mm"
include "mpbir2an.mm"

theorem idcnop
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( _I |` ~H ) e. ContOp

  proof
    cid
    chil
    cres
    #
    ccop
    wcel
    chil
    chil
    @0
    wf
    #
    vw
    cv
    #
    vx
    cv
    #
    cmv
    co
    #
    cno
    cfv
    #
    vz
    cv
    #
    clt
    wbr
    #
    @2
    @0
    cfv
    #
    @3
    @0
    cfv
    #
    cmv
    co
    #
    cno
    cfv
    #
    vy
    cv
    #
    clt
    wbr
    #
    wi
    #
    vw
    chil
    wral
    #
    vz
    crp
    wrex
    #
    vy
    crp
    wral
    vx
    chil
    wral
    chil
    chil
    @0
    wf1o
    @1
    chil
    f1oi
    chil
    chil
    @0
    f1of
    ax-mp
    @16
    vx
    vy
    chil
    crp
    @12
    crp
    wcel
    #
    @17
    @5
    @12
    clt
    wbr
    #
    @13
    wi
    #
    vw
    chil
    wral
    #
    @16
    @3
    chil
    wcel
    #
    @17
    id
    @21
    @19
    vw
    chil
    @21
    @2
    chil
    wcel
    #
    wa
    #
    @13
    @18
    @23
    @11
    @5
    @12
    clt
    @23
    @10
    @4
    cno
    @22
    @21
    @8
    @2
    @9
    @3
    cmv
    chil
    @2
    fvresi
    chil
    @3
    fvresi
    oveqan12rd
    fveq2d
    breq1d
    biimprd
    ralrimiva
    @15
    @20
    vz
    @12
    crp
    vz
    vy
    weq
    #
    @14
    @19
    vw
    chil
    @24
    @7
    @18
    @13
    @6
    @12
    @5
    clt
    breq2
    imbi1d
    ralbidv
    rspcev
    syl2anr
    rgen2
    vx
    vy
    vz
    vw
    @0
    elcnop
    mpbir2an
end
