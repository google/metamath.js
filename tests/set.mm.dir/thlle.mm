include "cvv.mm"
include "wcel.mm"
include "cple.mm"
include "cfv.mm"
include "wceq.mm"
include "cnx.mm"
include "coc.mm"
include "cocv.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "eqid.mm"
include "thlval.mm"
include "fveq2d.mm"
include "pleid.mm"
include "wne.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "10re.mm"
include "1nn0.mm"
include "0nn0.mm"
include "1nn.mm"
include "0lt1.mm"
include "declt.mm"
include "ltneii.mm"
include "plendx.mm"
include "ocndx.mm"
include "neeq12i.mm"
include "mpbir.mm"
include "setsnid.mm"
include "eqtri.mm"
include "syl6reqr.mm"
include "wn.mm"
include "c0.mm"
include "str0.mm"
include "cv.mm"
include "cpr.mm"
include "wss.mm"
include "wa.mm"
include "copab.mm"
include "ccss.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ipolerval.mm"
include "ax-mp.mm"
include "eqtr4i.mm"
include "wex.mm"
include "opabn0.mm"
include "vex.mm"
include "prss.mm"
include "elfvex.mm"
include "eleq2s.mm"
include "ad2antrr.mm"
include "sylanbr.mm"
include "exlimivv.mm"
include "sylbi.mm"
include "necon1bi.mm"
include "syl5eq.mm"
include "cthl.mm"
include "fvprc.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem thlle
  let cC: class C
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vh: setvar h
  let c.pe: class ._|_
  assume thlval.k: |- K = ( toHL ` W )
  assume thlbas.c: |- C = ( CSubSp ` W )
  assume thlle.i: |- I = ( toInc ` C )
  assume thlle.l: |- .<_ = ( le ` I )


  assert |- .<_ = ( le ` K )

  proof
    cW
    cvv
    wcel
    #
    c.le
    cK
    cple
    cfv
    #
    wceq
    @0
    @1
    cI
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
    cple
    cfv
    #
    c.le
    @0
    cK
    @4
    cple
    cC
    cI
    cK
    @3
    cvv
    cW
    thlval.k
    thlbas.c
    thlle.i
    @3
    eqid
    thlval
    fveq2d
    c.le
    cI
    cple
    cfv
    #
    @5
    thlle.l
    @3
    @2
    cple
    cI
    pleid
    cnx
    cple
    cfv
    #
    @2
    wne
    c1
    cc0
    cdc
    #
    c1
    c1
    cdc
    #
    wne
    @8
    @9
    10re
    c1
    cc0
    c1
    1nn0
    0nn0
    1nn
    0lt1
    declt
    ltneii
    @7
    @8
    @2
    @9
    plendx
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
    cple
    cfv
    c.le
    @1
    cple
    @7
    pleid
    str0
    @10
    c.le
    vx
    cv
    #
    vy
    cv
    #
    cpr
    cC
    wss
    #
    @11
    @12
    wss
    #
    wa
    #
    vx
    vy
    copab
    #
    c0
    c.le
    @6
    @16
    thlle.l
    cC
    cvv
    wcel
    @16
    @6
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
    vx
    vy
    cC
    cI
    cvv
    thlle.i
    ipolerval
    ax-mp
    eqtr4i
    @0
    @16
    c0
    @16
    c0
    wne
    @15
    vy
    wex
    vx
    wex
    @0
    @15
    vx
    vy
    opabn0
    @15
    @0
    vx
    vy
    @13
    @11
    cC
    wcel
    #
    @12
    cC
    wcel
    #
    wa
    @14
    @0
    @11
    @12
    cC
    vx
    vex
    vy
    vex
    prss
    @18
    @0
    @19
    @14
    @0
    @11
    @17
    cC
    @11
    cW
    ccss
    elfvex
    thlbas.c
    eleq2s
    ad2antrr
    sylanbr
    exlimivv
    sylbi
    necon1bi
    syl5eq
    @10
    cK
    c0
    cple
    @10
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
