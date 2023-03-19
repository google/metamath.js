include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "co.mm"
include "cfv.mm"
include "cpr.mm"
include "cglb.mm"
include "cv.mm"
include "ciin.mm"
include "cin.mm"
include "cbs.mm"
include "eqid.mm"
include "simpll.mm"
include "diadmclN.mm"
include "adantrr.mm"
include "adantrl.mm"
include "meetval.mm"
include "fveq2d.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "simpl.mm"
include "prssi.mm"
include "adantl.mm"
include "prnzg.mm"
include "ad2antrl.mm"
include "diaglbN.mm"
include "syl12anc.mm"
include "fveq2.mm"
include "iinxprg.mm"
include "3eqtrd.mm"

theorem diameetN
  let cH: class H
  let cI: class I
  let cK: class K
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let cY: class Y
  let vx: setvar x
  assume diam.m: |- ./\ = ( meet ` K )
  assume diam.h: |- H = ( LHyp ` K )
  assume diam.i: |- I = ( ( DIsoA ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. dom I /\ Y e. dom I ) ) -> ( I ` ( X ./\ Y ) ) = ( ( I ` X ) i^i ( I ` Y ) ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cX
    cI
    cdm
    #
    wcel
    #
    cY
    @3
    wcel
    #
    wa
    #
    wa
    #
    cX
    cY
    c.an
    co
    #
    cI
    cfv
    cX
    cY
    cpr
    #
    cK
    cglb
    cfv
    #
    cfv
    #
    cI
    cfv
    #
    vx
    @9
    vx
    cv
    #
    cI
    cfv
    #
    ciin
    #
    cX
    cI
    cfv
    #
    cY
    cI
    cfv
    #
    cin
    #
    @7
    @8
    @11
    cI
    @7
    @10
    cK
    c.an
    chlt
    cK
    cbs
    cfv
    #
    cX
    cY
    @19
    @10
    eqid
    #
    diam.m
    @0
    @1
    @6
    simpll
    @2
    @4
    cX
    @19
    wcel
    @5
    @19
    cH
    cI
    cK
    chlt
    cW
    cX
    @19
    eqid
    #
    diam.h
    diam.i
    diadmclN
    adantrr
    @2
    @5
    cY
    @19
    wcel
    @4
    @19
    cH
    cI
    cK
    chlt
    cW
    cY
    @21
    diam.h
    diam.i
    diadmclN
    adantrl
    meetval
    fveq2d
    @7
    @2
    @9
    @3
    wss
    #
    @9
    c0
    wne
    #
    @12
    @15
    wceq
    @2
    @6
    simpl
    @6
    @22
    @2
    cX
    cY
    @3
    prssi
    adantl
    @4
    @23
    @2
    @5
    cX
    cY
    @3
    prnzg
    ad2antrl
    vx
    @9
    @10
    cH
    cI
    cK
    cW
    @20
    diam.h
    diam.i
    diaglbN
    syl12anc
    @6
    @15
    @18
    wceq
    @2
    vx
    cX
    cY
    @14
    @16
    @17
    @3
    @3
    @13
    cX
    cI
    fveq2
    @13
    cY
    cI
    fveq2
    iinxprg
    adantl
    3eqtrd
end
