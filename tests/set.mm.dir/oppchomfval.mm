include "cvv.mm"
include "wcel.mm"
include "ctpos.mm"
include "chom.mm"
include "cfv.mm"
include "wceq.mm"
include "cnx.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cco.mm"
include "cbs.mm"
include "cxp.mm"
include "cv.mm"
include "c2nd.mm"
include "c1st.mm"
include "cmpt2.mm"
include "homid.mm"
include "wne.mm"
include "c1.mm"
include "c4.mm"
include "cdc.mm"
include "c5.mm"
include "1nn0.mm"
include "4nn.mm"
include "decnncl.mm"
include "nnrei.mm"
include "4nn0.mm"
include "5nn.mm"
include "4lt5.mm"
include "declt.mm"
include "ltneii.mm"
include "homndx.mm"
include "ccondx.mm"
include "neeq12i.mm"
include "mpbir.mm"
include "setsnid.mm"
include "fvex.mm"
include "eqeltri.mm"
include "tposex.mm"
include "setsid.mm"
include "mpan2.mm"
include "eqid.mm"
include "oppcval.mm"
include "fveq2d.mm"
include "3eqtr4a.mm"
include "wn.mm"
include "c0.mm"
include "tpos0.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "tposeqd.mm"
include "coppc.mm"
include "df-hom.mm"
include "str0.mm"
include "syl6eqr.mm"
include "pm2.61i.mm"

theorem oppchomfval
  let cC: class C
  let cH: class H
  let cO: class O
  let vu: setvar u
  let vz: setvar z
  assume oppchom.h: |- H = ( Hom ` C )
  assume oppchom.o: |- O = ( oppCat ` C )


  assert |- tpos H = ( Hom ` O )

  proof
    cC
    cvv
    wcel
    #
    cH
    ctpos
    #
    cO
    chom
    cfv
    #
    wceq
    @0
    cC
    cnx
    chom
    cfv
    #
    @1
    cop
    csts
    co
    #
    chom
    cfv
    #
    @4
    cnx
    cco
    cfv
    #
    vu
    vz
    cC
    cbs
    cfv
    #
    @7
    cxp
    @7
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
    chom
    cfv
    @1
    @2
    @10
    @6
    chom
    @4
    homid
    @3
    @6
    wne
    c1
    c4
    cdc
    #
    c1
    c5
    cdc
    #
    wne
    @12
    @13
    @12
    c1
    c4
    1nn0
    4nn
    decnncl
    nnrei
    c1
    c4
    c5
    1nn0
    4nn0
    5nn
    4lt5
    declt
    ltneii
    @3
    @12
    @6
    @13
    homndx
    ccondx
    neeq12i
    mpbir
    setsnid
    @0
    @1
    cvv
    wcel
    @1
    @5
    wceq
    cH
    cH
    cC
    chom
    cfv
    #
    cvv
    oppchom.h
    cC
    chom
    fvex
    eqeltri
    tposex
    cvv
    @1
    chom
    cvv
    cC
    homid
    setsid
    mpan2
    @0
    cO
    @11
    chom
    vz
    vu
    @7
    cC
    @9
    cH
    cO
    cvv
    @7
    eqid
    oppchom.h
    @9
    eqid
    oppchom.o
    oppcval
    fveq2d
    3eqtr4a
    @0
    wn
    #
    c0
    ctpos
    c0
    @1
    @2
    tpos0
    @15
    cH
    c0
    @15
    cH
    @14
    c0
    oppchom.h
    cC
    chom
    fvprc
    syl5eq
    tposeqd
    @15
    @2
    c0
    chom
    cfv
    c0
    @15
    cO
    c0
    chom
    @15
    cO
    cC
    coppc
    cfv
    c0
    oppchom.o
    cC
    coppc
    fvprc
    syl5eq
    fveq2d
    chom
    @12
    df-hom
    str0
    syl6eqr
    3eqtr4a
    pm2.61i
end
