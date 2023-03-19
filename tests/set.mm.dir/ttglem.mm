include "cvv.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "cnx.mm"
include "citv.mm"
include "cbs.mm"
include "cv.mm"
include "csg.mm"
include "co.mm"
include "cvsca.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "wrex.mm"
include "crab.mm"
include "cmpt2.mm"
include "cop.mm"
include "csts.mm"
include "clng.mm"
include "w3o.mm"
include "eqid.mm"
include "ttgval.mm"
include "simpld.mm"
include "fveq2d.mm"
include "ndxid.mm"
include "wne.mm"
include "c6.mm"
include "cdc.mm"
include "nnrei.mm"
include "ltneii.mm"
include "ndxarg.mm"
include "itvndx.mm"
include "neeq12i.mm"
include "mpbir.mm"
include "setsnid.mm"
include "c7.mm"
include "clt.mm"
include "wbr.mm"
include "1nn0.mm"
include "6nn0.mm"
include "7nn.mm"
include "6lt7.mm"
include "declt.mm"
include "6nn.mm"
include "decnncl.mm"
include "lttri.mm"
include "mp2an.mm"
include "lngndx.mm"
include "eqtri.mm"
include "syl6reqr.mm"
include "wn.mm"
include "c0.mm"
include "str0.mm"
include "fvprc.mm"
include "cttg.mm"
include "syl5eq.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem ttglem
  let cE: class E
  let cG: class G
  let cH: class H
  let cN: class N
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume ttgval.n: |- G = ( toTG ` H )
  assume ttglem.2: |- E = Slot N
  assume ttglem.3: |- N e. NN
  assume ttglem.4: |- N < ; 1 6


  assert |- ( E ` H ) = ( E ` G )

  proof
    cH
    cvv
    wcel
    #
    cH
    cE
    cfv
    #
    cG
    cE
    cfv
    #
    wceq
    @0
    @2
    cH
    cnx
    citv
    cfv
    #
    vx
    vy
    cH
    cbs
    cfv
    #
    @4
    vz
    cv
    #
    vx
    cv
    #
    cH
    csg
    cfv
    #
    co
    vk
    cv
    vy
    cv
    #
    @6
    @7
    co
    cH
    cvsca
    cfv
    #
    co
    wceq
    vk
    cc0
    c1
    cicc
    co
    wrex
    vz
    @4
    crab
    cmpt2
    #
    cop
    csts
    co
    #
    cnx
    clng
    cfv
    #
    vx
    vy
    @4
    @4
    @5
    @6
    @8
    cG
    citv
    cfv
    #
    co
    wcel
    @6
    @5
    @8
    @13
    co
    wcel
    @8
    @6
    @5
    @13
    co
    wcel
    w3o
    vz
    @4
    crab
    cmpt2
    #
    cop
    csts
    co
    #
    cE
    cfv
    #
    @1
    @0
    cG
    @15
    cE
    @0
    cG
    @15
    wceq
    @13
    @10
    wceq
    vx
    vy
    vz
    @4
    @9
    vk
    cG
    cH
    @13
    @7
    cvv
    ttgval.n
    @4
    eqid
    @7
    eqid
    @9
    eqid
    @13
    eqid
    ttgval
    simpld
    fveq2d
    @1
    @11
    cE
    cfv
    @16
    @10
    @3
    cE
    cH
    cE
    cN
    ttglem.2
    ttglem.3
    ndxid
    #
    cnx
    cE
    cfv
    #
    @3
    wne
    cN
    c1
    c6
    cdc
    #
    wne
    cN
    @19
    cN
    ttglem.3
    nnrei
    #
    ttglem.4
    ltneii
    @18
    cN
    @3
    @19
    cE
    cN
    ttglem.2
    ttglem.3
    ndxarg
    #
    itvndx
    neeq12i
    mpbir
    setsnid
    @14
    @12
    cE
    @11
    @17
    @18
    @12
    wne
    cN
    c1
    c7
    cdc
    #
    wne
    cN
    @22
    @20
    cN
    @19
    clt
    wbr
    @19
    @22
    clt
    wbr
    cN
    @22
    clt
    wbr
    ttglem.4
    c1
    c6
    c7
    1nn0
    6nn0
    7nn
    6lt7
    declt
    cN
    @19
    @22
    @20
    @19
    c1
    c6
    1nn0
    6nn
    decnncl
    nnrei
    @22
    c1
    c7
    1nn0
    7nn
    decnncl
    nnrei
    lttri
    mp2an
    ltneii
    @18
    cN
    @12
    @22
    @21
    lngndx
    neeq12i
    mpbir
    setsnid
    eqtri
    syl6reqr
    @0
    wn
    #
    c0
    c0
    cE
    cfv
    @1
    @2
    cE
    cN
    ttglem.2
    str0
    cH
    cE
    fvprc
    @23
    cG
    c0
    cE
    @23
    cG
    cH
    cttg
    cfv
    c0
    ttgval.n
    cH
    cttg
    fvprc
    syl5eq
    fveq2d
    3eqtr4a
    pm2.61i
end
