include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cv.mm"
include "wo.mm"
include "catm.mm"
include "cfv.mm"
include "cjn.mm"
include "cple.mm"
include "wbr.mm"
include "wrex.mm"
include "wss.mm"
include "wb.mm"
include "simpl.mm"
include "eqid.mm"
include "psubssat.mm"
include "elpadd.mm"
include "syl3anc.mm"
include "wi.mm"
include "pm1.2.mm"
include "a1i.mm"
include "psubspi.mm"
include "3exp1.mm"
include "imp4b.mm"
include "jaod.mm"
include "sylbid.mm"
include "ssrdv.mm"
include "sspadd1.mm"
include "eqssd.mm"

theorem paddidm
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let cK: class K
  let cX: class X
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let cY: class Y
  assume paddidm.s: |- S = ( PSubSp ` K )
  assume paddidm.p: |- .+ = ( +P ` K )


  assert |- ( ( K e. B /\ X e. S ) -> ( X .+ X ) = X )

  proof
    cK
    cB
    wcel
    #
    cX
    cS
    wcel
    #
    wa
    #
    cX
    cX
    c.pl
    co
    #
    cX
    @2
    vp
    @3
    cX
    @2
    vp
    cv
    #
    @3
    wcel
    #
    @4
    cX
    wcel
    #
    @6
    wo
    #
    @4
    cK
    catm
    cfv
    #
    wcel
    #
    @4
    vq
    cv
    vr
    cv
    cK
    cjn
    cfv
    #
    co
    cK
    cple
    cfv
    #
    wbr
    vr
    cX
    wrex
    vq
    cX
    wrex
    #
    wa
    #
    wo
    #
    @6
    @2
    @0
    cX
    @8
    wss
    #
    @15
    @5
    @14
    wb
    @0
    @1
    simpl
    #
    @8
    cB
    cS
    cK
    cX
    @8
    eqid
    #
    paddidm.s
    psubssat
    #
    @18
    @8
    cB
    c.pl
    @4
    @10
    cK
    @11
    cX
    cX
    vr
    vq
    @11
    eqid
    #
    @10
    eqid
    #
    @17
    paddidm.p
    elpadd
    syl3anc
    @2
    @7
    @6
    @13
    @7
    @6
    wi
    @2
    @6
    pm1.2
    a1i
    @0
    @1
    @9
    @12
    @6
    @0
    @1
    @9
    @12
    @6
    @8
    cB
    @4
    cS
    @10
    cK
    @11
    cX
    vr
    vq
    @19
    @20
    @17
    paddidm.s
    psubspi
    3exp1
    imp4b
    jaod
    sylbid
    ssrdv
    @2
    @0
    @15
    @15
    cX
    @3
    wss
    @16
    @18
    @18
    @8
    cB
    c.pl
    cK
    cX
    cX
    @17
    paddidm.p
    sspadd1
    syl3anc
    eqssd
end
