include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "w3a.mm"
include "copab.mm"
include "cop.mm"
include "cxp.mm"
include "crab.mm"
include "cdia.mm"
include "csn.mm"
include "cple.mm"
include "wbr.mm"
include "simpl.mm"
include "trlcl.mm"
include "eqid.mm"
include "trlle.mm"
include "dibval2.mm"
include "syl12anc.mm"
include "relxp.mm"
include "opelxp.mm"
include "dia1dim.mm"
include "abeq2d.mm"
include "anbi1d.mm"
include "tendocl.mm"
include "3expa.mm"
include "an32s.mm"
include "tendo0cl.mm"
include "ad2antrr.mm"
include "jca.mm"
include "eleq1.mm"
include "bi2anan9.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "pm4.71rd.mm"
include "velsn.mm"
include "anbi2i.mm"
include "r19.41v.mm"
include "bitr4i.mm"
include "df-3an.mm"
include "3bitr4g.mm"
include "bitrd.mm"
include "syl5bb.mm"
include "opabbi2dv.mm"
include "eqtrd.mm"
include "eqeq1.mm"
include "vex.mm"
include "opth.mm"
include "syl6bb.mm"
include "rexbidv.mm"
include "rabxp.mm"
include "syl6eqr.mm"

theorem dib1dim
  let cB: class B
  let cR: class R
  let cT: class T
  let vg: setvar g
  let vh: setvar h
  let cE: class E
  let cF: class F
  let cH: class H
  let cI: class I
  let cK: class K
  let cO: class O
  let cW: class W
  let vs: setvar s
  let vf: setvar f
  let vt: setvar t
  assume dib1dim.b: |- B = ( Base ` K )
  assume dib1dim.h: |- H = ( LHyp ` K )
  assume dib1dim.t: |- T = ( ( LTrn ` K ) ` W )
  assume dib1dim.r: |- R = ( ( trL ` K ) ` W )
  assume dib1dim.e: |- E = ( ( TEndo ` K ) ` W )
  assume dib1dim.o: |- O = ( h e. T |-> ( _I |` B ) )
  assume dib1dim.i: |- I = ( ( DIsoB ` K ) ` W )

  disjoint B h
  disjoint g s
  disjoint E g
  disjoint E s
  disjoint F g
  disjoint F s
  disjoint H s
  disjoint h s
  disjoint K h
  disjoint K s
  disjoint O g
  disjoint O s
  disjoint R s
  disjoint g h
  disjoint T g
  disjoint T h
  disjoint T s
  disjoint W h
  disjoint W s
  disjoint f g
  disjoint f s
  disjoint f t
  disjoint E f
  disjoint g t
  disjoint s t
  disjoint E t
  disjoint F f
  disjoint F t
  disjoint H f
  disjoint H t
  disjoint f h
  disjoint K f
  disjoint h t
  disjoint K t
  disjoint O f
  disjoint O t
  disjoint R f
  disjoint R t
  disjoint T f
  disjoint T t
  disjoint W f
  disjoint W t
  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T ) -> ( I ` ( R ` F ) ) = { g e. ( T X. E ) | E. s e. E g = <. ( s ` F ) , O >. } )

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
    #
    cI
    cfv
    #
    vf
    cv
    #
    cT
    wcel
    #
    vt
    cv
    #
    cE
    wcel
    #
    @5
    cF
    vs
    cv
    #
    cfv
    #
    wceq
    #
    @7
    cO
    wceq
    #
    wa
    #
    vs
    cE
    wrex
    #
    w3a
    #
    vf
    vt
    copab
    #
    vg
    cv
    #
    @10
    cO
    cop
    #
    wceq
    #
    vs
    cE
    wrex
    #
    vg
    cT
    cE
    cxp
    crab
    @2
    @4
    @3
    cW
    cK
    cdia
    cfv
    cfv
    #
    cfv
    #
    cO
    csn
    #
    cxp
    #
    @16
    @2
    @0
    @3
    cB
    wcel
    @3
    cW
    cK
    cple
    cfv
    #
    wbr
    @4
    @24
    wceq
    @0
    @1
    simpl
    cB
    cR
    cT
    cF
    cH
    cK
    cW
    dib1dim.b
    dib1dim.h
    dib1dim.t
    dib1dim.r
    trlcl
    cR
    cT
    cF
    cH
    cK
    @25
    cW
    @25
    eqid
    #
    dib1dim.h
    dib1dim.t
    dib1dim.r
    trlle
    cB
    cT
    vh
    cH
    cI
    @21
    cK
    @25
    chlt
    cW
    @3
    cO
    dib1dim.b
    @26
    dib1dim.h
    dib1dim.t
    dib1dim.o
    @21
    eqid
    #
    dib1dim.i
    dibval2
    syl12anc
    @2
    @15
    vf
    vt
    @24
    @22
    @23
    relxp
    @5
    @7
    cop
    #
    @24
    wcel
    @5
    @22
    wcel
    #
    @7
    @23
    wcel
    #
    wa
    #
    @2
    @15
    @5
    @7
    @22
    @23
    opelxp
    @2
    @31
    @11
    vs
    cE
    wrex
    #
    @30
    wa
    #
    @15
    @2
    @29
    @32
    @30
    @2
    @32
    vf
    @22
    cR
    cT
    vf
    cE
    cF
    cH
    @21
    cK
    cW
    vs
    dib1dim.h
    dib1dim.t
    dib1dim.r
    dib1dim.e
    @27
    dia1dim
    abeq2d
    anbi1d
    @2
    @14
    @6
    @8
    wa
    #
    @14
    wa
    @33
    @15
    @2
    @14
    @34
    @2
    @13
    @34
    vs
    cE
    @2
    @9
    cE
    wcel
    #
    wa
    #
    @34
    @13
    @10
    cT
    wcel
    #
    cO
    cE
    wcel
    #
    wa
    @36
    @37
    @38
    @0
    @35
    @1
    @37
    @0
    @35
    @1
    @37
    @9
    cT
    cE
    cF
    cH
    cK
    chlt
    cW
    dib1dim.h
    dib1dim.t
    dib1dim.e
    tendocl
    3expa
    an32s
    @0
    @38
    @1
    @35
    cB
    cT
    vh
    cE
    cH
    cK
    cO
    cW
    dib1dim.b
    dib1dim.h
    dib1dim.t
    dib1dim.e
    dib1dim.o
    tendo0cl
    ad2antrr
    jca
    @11
    @6
    @37
    @12
    @8
    @38
    @5
    @10
    cT
    eleq1
    @7
    cO
    cE
    eleq1
    bi2anan9
    syl5ibrcom
    rexlimdva
    pm4.71rd
    @33
    @32
    @12
    wa
    @14
    @30
    @12
    @32
    vt
    cO
    velsn
    anbi2i
    @11
    @12
    vs
    cE
    r19.41v
    bitr4i
    @6
    @8
    @14
    df-3an
    3bitr4g
    bitrd
    syl5bb
    opabbi2dv
    eqtrd
    @20
    @14
    vg
    vf
    vt
    cT
    cE
    @17
    @28
    wceq
    #
    @19
    @13
    vs
    cE
    @39
    @19
    @28
    @18
    wceq
    @13
    @17
    @28
    @18
    eqeq1
    @5
    @7
    @10
    cO
    vf
    vex
    vt
    vex
    opth
    syl6bb
    rexbidv
    rabxp
    syl6eqr
end
