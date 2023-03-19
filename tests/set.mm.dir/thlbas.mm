include "cvv.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "cipo.mm"
include "cnx.mm"
include "coc.mm"
include "cocv.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "eqid.mm"
include "thlval.mm"
include "fveq2d.mm"
include "ccss.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ipobas.mm"
include "ax-mp.mm"
include "baseid.mm"
include "wne.mm"
include "c1.mm"
include "cdc.mm"
include "1re.mm"
include "1nn.mm"
include "1nn0.mm"
include "1lt10.mm"
include "declti.mm"
include "ltneii.mm"
include "basendx.mm"
include "ocndx.mm"
include "neeq12i.mm"
include "mpbir.mm"
include "setsnid.mm"
include "eqtri.mm"
include "syl6reqr.mm"
include "wn.mm"
include "c0.mm"
include "base0.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "cthl.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem thlbas
  let cC: class C
  let cK: class K
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vh: setvar h
  let cI: class I
  let c.pe: class ._|_
  assume thlval.k: |- K = ( toHL ` W )
  assume thlbas.c: |- C = ( CSubSp ` W )


  assert |- C = ( Base ` K )

  proof
    cW
    cvv
    wcel
    #
    cC
    cK
    cbs
    cfv
    #
    wceq
    @0
    @1
    cC
    cipo
    cfv
    #
    cnx
    coc
    cfv
    #
    cW
    cocv
    cfv
    #
    cop
    csts
    co
    #
    cbs
    cfv
    #
    cC
    @0
    cK
    @5
    cbs
    cC
    @2
    cK
    @4
    cvv
    cW
    thlval.k
    thlbas.c
    @2
    eqid
    #
    @4
    eqid
    thlval
    fveq2d
    cC
    @2
    cbs
    cfv
    #
    @6
    cC
    cvv
    wcel
    cC
    @8
    wceq
    cC
    cW
    ccss
    cfv
    #
    cvv
    thlbas.c
    cW
    ccss
    fvex
    eqeltri
    cC
    @2
    cvv
    @7
    ipobas
    ax-mp
    @4
    @3
    cbs
    @2
    baseid
    cnx
    cbs
    cfv
    #
    @3
    wne
    c1
    c1
    c1
    cdc
    #
    wne
    c1
    @11
    1re
    c1
    c1
    c1
    1nn
    1nn0
    1nn0
    1lt10
    declti
    ltneii
    @10
    c1
    @3
    @11
    basendx
    ocndx
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
    cbs
    cfv
    cC
    @1
    base0
    @12
    cC
    @9
    c0
    thlbas.c
    cW
    ccss
    fvprc
    syl5eq
    @12
    cK
    c0
    cbs
    @12
    cK
    cW
    cthl
    cfv
    c0
    thlval.k
    cW
    cthl
    fvprc
    syl5eq
    fveq2d
    3eqtr4a
    pm2.61i
end
