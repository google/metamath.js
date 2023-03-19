include "cvv.mm"
include "wcel.mm"
include "ccom.mm"
include "cds.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cnx.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cts.mm"
include "cmopn.mm"
include "dsid.mm"
include "wne.mm"
include "c1.mm"
include "c2.mm"
include "cdc.mm"
include "c9.mm"
include "9re.mm"
include "1nn.mm"
include "2nn0.mm"
include "9nn0.mm"
include "9lt10.mm"
include "declti.mm"
include "gtneii.mm"
include "dsndx.mm"
include "tsetndx.mm"
include "neeq12i.mm"
include "mpbir.mm"
include "setsnid.mm"
include "csg.mm"
include "fvex.mm"
include "eqeltri.mm"
include "coexg.mm"
include "mpan2.mm"
include "setsid.mm"
include "sylan2.mm"
include "eqid.mm"
include "tngval.mm"
include "fveq2d.mm"
include "3eqtr4a.mm"
include "wn.mm"
include "c0.mm"
include "co02.mm"
include "df-ds.mm"
include "str0.mm"
include "eqtri.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "coeq2d.mm"
include "ctng.mm"
include "reldmtng.mm"
include "ovprc1.mm"
include "adantr.mm"
include "pm2.61ian.mm"

theorem tngds
  let cT: class T
  let cG: class G
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume tngbas.t: |- T = ( G toNrmGrp N )
  assume tngds.2: |- .- = ( -g ` G )


  assert |- ( N e. V -> ( N o. .- ) = ( dist ` T ) )

  proof
    cG
    cvv
    wcel
    #
    cN
    cV
    wcel
    #
    cN
    c.mi
    ccom
    #
    cT
    cds
    cfv
    #
    wceq
    #
    @0
    @1
    wa
    #
    cG
    cnx
    cds
    cfv
    #
    @2
    cop
    csts
    co
    #
    cds
    cfv
    #
    @7
    cnx
    cts
    cfv
    #
    @2
    cmopn
    cfv
    #
    cop
    csts
    co
    #
    cds
    cfv
    @2
    @3
    @10
    @9
    cds
    @7
    dsid
    @6
    @9
    wne
    c1
    c2
    cdc
    #
    c9
    wne
    c9
    @12
    9re
    c1
    c2
    c9
    1nn
    2nn0
    9nn0
    9lt10
    declti
    gtneii
    @6
    @12
    @9
    c9
    dsndx
    tsetndx
    neeq12i
    mpbir
    setsnid
    @1
    @0
    @2
    cvv
    wcel
    #
    @2
    @8
    wceq
    @1
    c.mi
    cvv
    wcel
    @13
    c.mi
    cG
    csg
    cfv
    #
    cvv
    tngds.2
    cG
    csg
    fvex
    eqeltri
    cN
    c.mi
    cV
    cvv
    coexg
    mpan2
    cvv
    @2
    cds
    cvv
    cG
    dsid
    setsid
    sylan2
    @5
    cT
    @11
    cds
    @2
    cT
    cG
    @10
    c.mi
    cN
    cvv
    cV
    tngbas.t
    tngds.2
    @2
    eqid
    @10
    eqid
    tngval
    fveq2d
    3eqtr4a
    @0
    wn
    #
    @4
    @1
    @15
    cN
    c0
    ccom
    #
    c0
    cds
    cfv
    #
    @2
    @3
    @16
    c0
    @17
    cN
    co02
    cds
    @12
    df-ds
    str0
    eqtri
    @15
    c.mi
    c0
    cN
    @15
    c.mi
    @14
    c0
    tngds.2
    cG
    csg
    fvprc
    syl5eq
    coeq2d
    @15
    cT
    c0
    cds
    @15
    cT
    cG
    cN
    ctng
    co
    c0
    tngbas.t
    cG
    cN
    ctng
    reldmtng
    ovprc1
    syl5eq
    fveq2d
    3eqtr4a
    adantr
    pm2.61ian
end
