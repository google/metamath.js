include "cbs.mm"
include "cfv.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cnx.mm"
include "chom.mm"
include "ctpos.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cco.mm"
include "cxp.mm"
include "cv.mm"
include "c2nd.mm"
include "c1st.mm"
include "cmpt2.mm"
include "eqid.mm"
include "oppcval.mm"
include "fveq2d.mm"
include "baseid.mm"
include "wne.mm"
include "c1.mm"
include "c4.mm"
include "cdc.mm"
include "1re.mm"
include "1nn.mm"
include "4nn0.mm"
include "1nn0.mm"
include "1lt10.mm"
include "declti.mm"
include "ltneii.mm"
include "basendx.mm"
include "homndx.mm"
include "neeq12i.mm"
include "mpbir.mm"
include "setsnid.mm"
include "c5.mm"
include "clt.mm"
include "wbr.mm"
include "5nn.mm"
include "4lt5.mm"
include "declt.mm"
include "4nn.mm"
include "decnncl.mm"
include "nnrei.mm"
include "lttri.mm"
include "mp2an.mm"
include "ccondx.mm"
include "eqtri.mm"
include "syl6reqr.mm"
include "wn.mm"
include "c0.mm"
include "base0.mm"
include "fvprc.mm"
include "coppc.mm"
include "syl5eq.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem oppcbas
  let cB: class B
  let cC: class C
  let cO: class O
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vu: setvar u
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume oppcbas.1: |- O = ( oppCat ` C )
  assume oppcbas.2: |- B = ( Base ` C )


  assert |- B = ( Base ` O )

  proof
    cB
    cC
    cbs
    cfv
    #
    cO
    cbs
    cfv
    #
    oppcbas.2
    cC
    cvv
    wcel
    #
    @0
    @1
    wceq
    @2
    @1
    cC
    cnx
    chom
    cfv
    #
    cC
    chom
    cfv
    #
    ctpos
    #
    cop
    csts
    co
    #
    cnx
    cco
    cfv
    #
    vu
    vz
    @0
    @0
    cxp
    @0
    vz
    cv
    vu
    cv
    #
    c2nd
    cfv
    cop
    @8
    c1st
    cfv
    cC
    cco
    cfv
    #
    co
    ctpos
    cmpt2
    #
    cop
    csts
    co
    #
    cbs
    cfv
    #
    @0
    @2
    cO
    @11
    cbs
    vz
    vu
    @0
    cC
    @9
    @4
    cO
    cvv
    @0
    eqid
    @4
    eqid
    @9
    eqid
    oppcbas.1
    oppcval
    fveq2d
    @0
    @6
    cbs
    cfv
    @12
    @5
    @3
    cbs
    cC
    baseid
    cnx
    cbs
    cfv
    #
    @3
    wne
    c1
    c1
    c4
    cdc
    #
    wne
    c1
    @14
    1re
    c1
    c4
    c1
    1nn
    4nn0
    1nn0
    1lt10
    declti
    #
    ltneii
    @13
    c1
    @3
    @14
    basendx
    homndx
    neeq12i
    mpbir
    setsnid
    @10
    @7
    cbs
    @6
    baseid
    @13
    @7
    wne
    c1
    c1
    c5
    cdc
    #
    wne
    c1
    @16
    1re
    c1
    @14
    clt
    wbr
    @14
    @16
    clt
    wbr
    c1
    @16
    clt
    wbr
    @15
    c1
    c4
    c5
    1nn0
    4nn0
    5nn
    4lt5
    declt
    c1
    @14
    @16
    1re
    @14
    c1
    c4
    1nn0
    4nn
    decnncl
    nnrei
    @16
    c1
    c5
    1nn0
    5nn
    decnncl
    nnrei
    lttri
    mp2an
    ltneii
    @13
    c1
    @7
    @16
    basendx
    ccondx
    neeq12i
    mpbir
    setsnid
    eqtri
    syl6reqr
    @2
    wn
    #
    c0
    c0
    cbs
    cfv
    @0
    @1
    base0
    cC
    cbs
    fvprc
    @17
    cO
    c0
    cbs
    @17
    cO
    cC
    coppc
    cfv
    c0
    oppcbas.1
    cC
    coppc
    fvprc
    syl5eq
    fveq2d
    3eqtr4a
    pm2.61i
    eqtri
end
