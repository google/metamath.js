include "cvv.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cnx.mm"
include "cds.mm"
include "csg.mm"
include "ccom.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "cts.mm"
include "cmopn.mm"
include "eqid.mm"
include "tngval.mm"
include "fveq2d.mm"
include "ndxid.mm"
include "c1.mm"
include "c2.mm"
include "cdc.mm"
include "cr.mm"
include "ndxarg.mm"
include "nnrei.mm"
include "eqeltri.mm"
include "c9.mm"
include "clt.mm"
include "wbr.mm"
include "eqbrtri.mm"
include "1nn.mm"
include "2nn0.mm"
include "9nn0.mm"
include "9lt10.mm"
include "declti.mm"
include "9re.mm"
include "1nn0.mm"
include "deccl.mm"
include "nn0rei.mm"
include "lttri.mm"
include "mp2an.mm"
include "ltneii.mm"
include "dsndx.mm"
include "neeqtrri.mm"
include "setsnid.mm"
include "tsetndx.mm"
include "eqtri.mm"
include "syl6reqr.mm"
include "wn.mm"
include "c0.mm"
include "str0.mm"
include "fvprc.mm"
include "adantr.mm"
include "ctng.mm"
include "reldmtng.mm"
include "ovprc1.mm"
include "syl5eq.mm"
include "3eqtr4a.mm"
include "pm2.61ian.mm"

theorem tnglem
  let cT: class T
  let cE: class E
  let cG: class G
  let cK: class K
  let cN: class N
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume tngbas.t: |- T = ( G toNrmGrp N )
  assume tnglem.2: |- E = Slot K
  assume tnglem.3: |- K e. NN
  assume tnglem.4: |- K < 9


  assert |- ( N e. V -> ( E ` G ) = ( E ` T ) )

  proof
    cG
    cvv
    wcel
    #
    cN
    cV
    wcel
    #
    cG
    cE
    cfv
    #
    cT
    cE
    cfv
    #
    wceq
    @0
    @1
    wa
    #
    @3
    cG
    cnx
    cds
    cfv
    #
    cN
    cG
    csg
    cfv
    #
    ccom
    #
    cop
    csts
    co
    #
    cnx
    cts
    cfv
    #
    @7
    cmopn
    cfv
    #
    cop
    csts
    co
    #
    cE
    cfv
    #
    @2
    @4
    cT
    @11
    cE
    @7
    cT
    cG
    @10
    @6
    cN
    cvv
    cV
    tngbas.t
    @6
    eqid
    @7
    eqid
    @10
    eqid
    tngval
    fveq2d
    @2
    @8
    cE
    cfv
    @12
    @7
    @5
    cE
    cG
    cE
    cK
    tnglem.2
    tnglem.3
    ndxid
    #
    cnx
    cE
    cfv
    #
    c1
    c2
    cdc
    #
    @5
    @14
    @15
    @14
    cK
    cr
    cE
    cK
    tnglem.2
    tnglem.3
    ndxarg
    #
    cK
    tnglem.3
    nnrei
    eqeltri
    #
    @14
    c9
    clt
    wbr
    c9
    @15
    clt
    wbr
    @14
    @15
    clt
    wbr
    @14
    cK
    c9
    clt
    @16
    tnglem.4
    eqbrtri
    #
    c1
    c2
    c9
    1nn
    2nn0
    9nn0
    9lt10
    declti
    @14
    c9
    @15
    @17
    9re
    @15
    c1
    c2
    1nn0
    2nn0
    deccl
    nn0rei
    lttri
    mp2an
    ltneii
    dsndx
    neeqtrri
    setsnid
    @10
    @9
    cE
    @8
    @13
    @14
    c9
    @9
    @14
    c9
    @17
    @18
    ltneii
    tsetndx
    neeqtrri
    setsnid
    eqtri
    syl6reqr
    @0
    wn
    #
    @1
    wa
    #
    c0
    c0
    cE
    cfv
    @2
    @3
    cE
    cK
    tnglem.2
    str0
    @19
    @2
    c0
    wceq
    @1
    cG
    cE
    fvprc
    adantr
    @20
    cT
    c0
    cE
    @20
    cT
    cG
    cN
    ctng
    co
    #
    c0
    tngbas.t
    @19
    @21
    c0
    wceq
    @1
    cG
    cN
    ctng
    reldmtng
    ovprc1
    adantr
    syl5eq
    fveq2d
    3eqtr4a
    pm2.61ian
end
