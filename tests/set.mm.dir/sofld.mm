include "wor.mm"
include "cxp.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "wa.mm"
include "wn.mm"
include "wceq.mm"
include "wrel.mm"
include "relxp.mm"
include "relss.mm"
include "mpi.mm"
include "ad2antlr.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wbr.mm"
include "df-br.mm"
include "csn.mm"
include "cdif.mm"
include "ssun1.mm"
include "undif1.mm"
include "sseqtr4i.mm"
include "simpll.mm"
include "dmss.mm"
include "dmxpid.mm"
include "syl6sseq.mm"
include "releldm.mm"
include "sylancom.mm"
include "sseldd.mm"
include "sossfld.mm"
include "syl2anc.mm"
include "sseldi.mm"
include "snssd.mm"
include "unssd.mm"
include "syl5ss.mm"
include "ex.mm"
include "syl5bir.mm"
include "con3dimp.mm"
include "pm2.21d.mm"
include "relssdv.mm"
include "ss0.mm"
include "syl.mm"
include "necon1ad.mm"
include "3impia.mm"
include "rnss.mm"
include "rnxpid.mm"
include "3ad2ant2.mm"
include "eqssd.mm"

theorem sofld
  let cA: class A
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let cB: class B


  assert |- ( ( R Or A /\ R C_ ( A X. A ) /\ R =/= (/) ) -> A = ( dom R u. ran R ) )

  proof
    cA
    cR
    wor
    #
    cR
    cA
    cA
    cxp
    #
    wss
    #
    cR
    c0
    wne
    #
    w3a
    cA
    cR
    cdm
    #
    cR
    crn
    #
    cun
    #
    @0
    @2
    @3
    cA
    @6
    wss
    #
    @0
    @2
    wa
    #
    @7
    cR
    c0
    @8
    @7
    wn
    #
    cR
    c0
    wceq
    #
    @8
    @9
    wa
    #
    cR
    c0
    wss
    @10
    @11
    vx
    vy
    cR
    c0
    @2
    cR
    wrel
    #
    @0
    @9
    @2
    @1
    wrel
    @12
    cA
    cA
    relxp
    cR
    @1
    relss
    mpi
    #
    ad2antlr
    @11
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    cR
    wcel
    #
    @16
    c0
    wcel
    @8
    @17
    @7
    @17
    @14
    @15
    cR
    wbr
    #
    @8
    @7
    @14
    @15
    cR
    df-br
    @8
    @18
    @7
    @8
    @18
    wa
    #
    cA
    cA
    @14
    csn
    #
    cdif
    #
    @20
    cun
    #
    @6
    cA
    cA
    @20
    cun
    @22
    cA
    @20
    ssun1
    cA
    @20
    undif1
    sseqtr4i
    @19
    @21
    @20
    @6
    @19
    @0
    @14
    cA
    wcel
    @21
    @6
    wss
    @0
    @2
    @18
    simpll
    @19
    @4
    cA
    @14
    @2
    @4
    cA
    wss
    @0
    @18
    @2
    @4
    @1
    cdm
    cA
    cR
    @1
    dmss
    cA
    dmxpid
    syl6sseq
    #
    ad2antlr
    @8
    @18
    @12
    @14
    @4
    wcel
    @2
    @12
    @0
    @18
    @13
    ad2antlr
    @14
    @15
    cR
    releldm
    sylancom
    #
    sseldd
    cA
    @14
    cR
    sossfld
    syl2anc
    @19
    @14
    @6
    @19
    @4
    @6
    @14
    @4
    @5
    ssun1
    @24
    sseldi
    snssd
    unssd
    syl5ss
    ex
    syl5bir
    con3dimp
    pm2.21d
    relssdv
    cR
    ss0
    syl
    ex
    necon1ad
    3impia
    @2
    @0
    @6
    cA
    wss
    @3
    @2
    @4
    @5
    cA
    @23
    @2
    @5
    @1
    crn
    cA
    cR
    @1
    rnss
    cA
    rnxpid
    syl6sseq
    unssd
    3ad2ant2
    eqssd
end
