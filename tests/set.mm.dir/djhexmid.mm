include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cfv.mm"
include "co.mm"
include "cin.mm"
include "wceq.mm"
include "simpl.mm"
include "simpr.mm"
include "dochssv.mm"
include "djhval.mm"
include "syl12anc.mm"
include "c0g.mm"
include "csn.mm"
include "clss.mm"
include "eqid.mm"
include "dochlss.mm"
include "dochnoncon.mm"
include "syldan.mm"
include "doch1.mm"
include "adantr.mm"
include "eqtr4d.mm"
include "fveq2d.mm"
include "cdih.mm"
include "crn.mm"
include "dih1rn.mm"
include "dochoc.mm"
include "3eqtrd.mm"

theorem djhexmid
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  assume djhexmid.h: |- H = ( LHyp ` K )
  assume djhexmid.u: |- U = ( ( DVecH ` K ) ` W )
  assume djhexmid.v: |- V = ( Base ` U )
  assume djhexmid.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume djhexmid.j: |- .\/ = ( ( joinH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X C_ V ) -> ( X .\/ ( ._|_ ` X ) ) = V )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cV
    wss
    #
    wa
    #
    cX
    cX
    c.pe
    cfv
    #
    c.or
    co
    #
    @3
    @3
    c.pe
    cfv
    cin
    #
    c.pe
    cfv
    #
    cV
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    cV
    @2
    @0
    @1
    @3
    cV
    wss
    @4
    @6
    wceq
    @0
    @1
    simpl
    @0
    @1
    simpr
    cU
    cH
    cK
    c.pe
    cV
    cW
    cX
    djhexmid.h
    djhexmid.u
    djhexmid.v
    djhexmid.o
    dochssv
    cU
    cH
    c.or
    cK
    c.pe
    cV
    cW
    cX
    @3
    djhexmid.h
    djhexmid.u
    djhexmid.v
    djhexmid.o
    djhexmid.j
    djhval
    syl12anc
    @2
    @5
    @7
    c.pe
    @2
    @5
    cU
    c0g
    cfv
    #
    csn
    #
    @7
    @0
    @1
    @3
    cU
    clss
    cfv
    #
    wcel
    @5
    @10
    wceq
    @11
    cU
    cH
    cK
    c.pe
    cV
    cW
    cX
    djhexmid.h
    djhexmid.u
    djhexmid.v
    @11
    eqid
    #
    djhexmid.o
    dochlss
    @11
    cU
    cH
    cK
    c.pe
    cW
    @3
    @9
    djhexmid.h
    djhexmid.u
    @12
    @9
    eqid
    #
    djhexmid.o
    dochnoncon
    syldan
    @0
    @7
    @10
    wceq
    @1
    cU
    cH
    cK
    c.pe
    cV
    cW
    @9
    djhexmid.h
    djhexmid.u
    djhexmid.o
    djhexmid.v
    @13
    doch1
    adantr
    eqtr4d
    fveq2d
    @0
    @1
    cV
    cW
    cK
    cdih
    cfv
    cfv
    #
    crn
    wcel
    #
    @8
    cV
    wceq
    @0
    @15
    @1
    cU
    cH
    @14
    cK
    cV
    cW
    djhexmid.h
    @14
    eqid
    #
    djhexmid.u
    djhexmid.v
    dih1rn
    adantr
    cH
    @14
    cK
    c.pe
    cW
    cV
    djhexmid.h
    @16
    djhexmid.o
    dochoc
    syldan
    3eqtrd
end
