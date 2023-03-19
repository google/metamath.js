include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "cop.mm"
include "cvsca.mm"
include "co.mm"
include "wceq.mm"
include "csca.mm"
include "cbs.mm"
include "wrex.mm"
include "cab.mm"
include "csn.mm"
include "ctendo.mm"
include "cxp.mm"
include "crab.mm"
include "df-rab.mm"
include "eqid.mm"
include "dib1dim.mm"
include "dvhbase.mm"
include "adantr.mm"
include "rexeqdv.mm"
include "ccom.mm"
include "simpll.mm"
include "simpr.mm"
include "simplr.mm"
include "tendo0cl.mm"
include "ad2antrr.mm"
include "dvhopvsca.mm"
include "syl13anc.mm"
include "tendo0mulr.mm"
include "adantlr.mm"
include "opeq2d.mm"
include "eqtrd.mm"
include "eqeq2d.mm"
include "rexbidva.mm"
include "wi.mm"
include "tendocl.mm"
include "3expa.mm"
include "an32s.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "eleq1a.mm"
include "syl.mm"
include "rexlimdva.mm"
include "pm4.71rd.mm"
include "3bitrd.mm"
include "abbidv.mm"
include "3eqtr4a.mm"
include "clmod.mm"
include "simpl.mm"
include "dvhlmod.mm"
include "dvhelvbasei.mm"
include "syl12anc.mm"
include "lspsn.mm"
include "eqtr4d.mm"

theorem dib1dim2
  let cB: class B
  let cR: class R
  let cT: class T
  let cU: class U
  let vh: setvar h
  let cF: class F
  let cH: class H
  let cI: class I
  let cK: class K
  let cN: class N
  let cO: class O
  let cW: class W
  let vu: setvar u
  let vv: setvar v
  assume dib1dim2.b: |- B = ( Base ` K )
  assume dib1dim2.h: |- H = ( LHyp ` K )
  assume dib1dim2.t: |- T = ( ( LTrn ` K ) ` W )
  assume dib1dim2.r: |- R = ( ( trL ` K ) ` W )
  assume dib1dim2.o: |- O = ( h e. T |-> ( _I |` B ) )
  assume dib1dim2.u: |- U = ( ( DVecH ` K ) ` W )
  assume dib1dim2.i: |- I = ( ( DIsoB ` K ) ` W )
  assume dib1dim2.n: |- N = ( LSpan ` U )

  disjoint B h
  disjoint K h
  disjoint T h
  disjoint W h
  disjoint u v
  disjoint F u
  disjoint F v
  disjoint H u
  disjoint H v
  disjoint h u
  disjoint h v
  disjoint K u
  disjoint K v
  disjoint N u
  disjoint N v
  disjoint R v
  disjoint O u
  disjoint O v
  disjoint T u
  disjoint T v
  disjoint U u
  disjoint U v
  disjoint W u
  disjoint W v
  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T ) -> ( I ` ( R ` F ) ) = ( N ` { <. F , O >. } ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cF
    cT
    wcel
    #
    wa
    #
    cF
    cR
    cfv
    cI
    cfv
    #
    vu
    cv
    #
    vv
    cv
    #
    cF
    cO
    cop
    #
    cU
    cvsca
    cfv
    #
    co
    #
    wceq
    #
    vv
    cU
    csca
    cfv
    #
    cbs
    cfv
    #
    wrex
    #
    vu
    cab
    #
    @6
    csn
    cN
    cfv
    #
    @2
    @4
    cF
    @5
    cfv
    #
    cO
    cop
    #
    wceq
    #
    vv
    cW
    cK
    ctendo
    cfv
    cfv
    #
    wrex
    #
    vu
    cT
    @18
    cxp
    #
    crab
    @4
    @20
    wcel
    #
    @19
    wa
    #
    vu
    cab
    @3
    @13
    @19
    vu
    @20
    df-rab
    cB
    cR
    cT
    vu
    vh
    @18
    cF
    cH
    cI
    cK
    cO
    cW
    vv
    dib1dim2.b
    dib1dim2.h
    dib1dim2.t
    dib1dim2.r
    @18
    eqid
    #
    dib1dim2.o
    dib1dim2.i
    dib1dim
    @2
    @12
    @22
    vu
    @2
    @12
    @9
    vv
    @18
    wrex
    @19
    @22
    @2
    @9
    vv
    @11
    @18
    @0
    @11
    @18
    wceq
    @1
    @11
    cU
    @18
    @10
    cH
    cK
    cW
    chlt
    dib1dim2.h
    @23
    dib1dim2.u
    @10
    eqid
    #
    @11
    eqid
    #
    dvhbase
    adantr
    rexeqdv
    @2
    @9
    @17
    vv
    @18
    @2
    @5
    @18
    wcel
    #
    wa
    #
    @8
    @16
    @4
    @27
    @8
    @15
    @5
    cO
    ccom
    #
    cop
    #
    @16
    @27
    @0
    @26
    @1
    cO
    @18
    wcel
    #
    @8
    @29
    wceq
    @0
    @1
    @26
    simpll
    @2
    @26
    simpr
    @0
    @1
    @26
    simplr
    @0
    @30
    @1
    @26
    cB
    cT
    vh
    @18
    cH
    cK
    cO
    cW
    dib1dim2.b
    dib1dim2.h
    dib1dim2.t
    @23
    dib1dim2.o
    tendo0cl
    #
    ad2antrr
    #
    @5
    cT
    @7
    cU
    @18
    cF
    cH
    cK
    chlt
    cW
    cO
    dib1dim2.h
    dib1dim2.t
    @23
    dib1dim2.u
    @7
    eqid
    #
    dvhopvsca
    syl13anc
    @27
    @28
    cO
    @15
    @0
    @26
    @28
    cO
    wceq
    @1
    cB
    cT
    @5
    vh
    @18
    cH
    cK
    cO
    cW
    dib1dim2.b
    dib1dim2.h
    dib1dim2.t
    @23
    dib1dim2.o
    tendo0mulr
    adantlr
    opeq2d
    eqtrd
    eqeq2d
    rexbidva
    @2
    @19
    @21
    @2
    @17
    @21
    vv
    @18
    @27
    @16
    @20
    wcel
    #
    @17
    @21
    wi
    @27
    @15
    cT
    wcel
    #
    @30
    @34
    @0
    @26
    @1
    @35
    @0
    @26
    @1
    @35
    @5
    cT
    @18
    cF
    cH
    cK
    chlt
    cW
    dib1dim2.h
    dib1dim2.t
    @23
    tendocl
    3expa
    an32s
    @32
    @15
    cO
    cT
    @18
    opelxpi
    syl2anc
    @16
    @20
    @4
    eleq1a
    syl
    rexlimdva
    pm4.71rd
    3bitrd
    abbidv
    3eqtr4a
    @2
    cU
    clmod
    wcel
    @6
    cU
    cbs
    cfv
    #
    wcel
    #
    @14
    @13
    wceq
    @2
    cU
    cH
    cK
    cW
    dib1dim2.h
    dib1dim2.u
    @0
    @1
    simpl
    #
    dvhlmod
    @2
    @0
    @1
    @30
    @37
    @38
    @0
    @1
    simpr
    @0
    @30
    @1
    @31
    adantr
    cO
    cT
    cU
    @18
    cF
    cH
    cK
    @36
    cW
    chlt
    dib1dim2.h
    dib1dim2.t
    @23
    dib1dim2.u
    @36
    eqid
    #
    dvhelvbasei
    syl12anc
    vu
    @7
    vv
    @10
    @11
    cN
    @36
    cU
    @6
    @24
    @25
    @39
    @33
    dib1dim2.n
    lspsn
    syl2anc
    eqtr4d
end
