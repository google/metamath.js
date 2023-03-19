include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "ciin.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cglb.mm"
include "polvalN.mm"
include "cbs.mm"
include "wral.mm"
include "cops.mm"
include "hlop.mm"
include "ad2antrr.mm"
include "ssel2.mm"
include "adantll.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "opoccl.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "pmapglb2xN.mm"
include "syldan.mm"
include "glbconxN.mm"
include "weq.mm"
include "opococ.mm"
include "eqeq2d.mm"
include "rexbidva.mm"
include "abbidv.mm"
include "wex.mm"
include "df-rex.mm"
include "equcom.mm"
include "anbi2i.mm"
include "ancom.mm"
include "bitri.mm"
include "exbii.mm"
include "vex.mm"
include "eleq1.mm"
include "ceqsexv.mm"
include "3bitri.mm"
include "abbii.mm"
include "abid2.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "3eqtr2d.mm"

theorem polval2N
  let cA: class A
  let cP: class P
  let cU: class U
  let cK: class K
  let cM: class M
  let c.pe: class ._|_
  let cX: class X
  let vp: setvar p
  let vx: setvar x
  assume polval2.u: |- U = ( lub ` K )
  assume polval2.o: |- ._|_ = ( oc ` K )
  assume polval2.a: |- A = ( Atoms ` K )
  assume polval2.m: |- M = ( pmap ` K )
  assume polval2.p: |- P = ( _|_P ` K )


  assert |- ( ( K e. HL /\ X C_ A ) -> ( P ` X ) = ( M ` ( ._|_ ` ( U ` X ) ) ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cA
    wss
    #
    wa
    #
    cX
    cP
    cfv
    cA
    vp
    cX
    vp
    cv
    #
    c.pe
    cfv
    #
    cM
    cfv
    ciin
    cin
    #
    vx
    cv
    #
    @4
    wceq
    vp
    cX
    wrex
    vx
    cab
    cK
    cglb
    cfv
    #
    cfv
    #
    cM
    cfv
    #
    cX
    cU
    cfv
    #
    c.pe
    cfv
    #
    cM
    cfv
    cA
    chlt
    cP
    cK
    cM
    c.pe
    cX
    vp
    polval2.o
    polval2.a
    polval2.m
    polval2.p
    polvalN
    @0
    @1
    @4
    cK
    cbs
    cfv
    #
    wcel
    #
    vp
    cX
    wral
    #
    @9
    @5
    wceq
    @2
    @13
    vp
    cX
    @2
    @3
    cX
    wcel
    #
    wa
    #
    cK
    cops
    wcel
    #
    @3
    @12
    wcel
    #
    @13
    @0
    @17
    @1
    @15
    cK
    hlop
    ad2antrr
    #
    @16
    @3
    cA
    wcel
    #
    @18
    @1
    @15
    @20
    @0
    cX
    cA
    @3
    ssel2
    adantll
    cA
    @12
    @3
    cK
    @12
    eqid
    #
    polval2.a
    atbase
    syl
    #
    @12
    cK
    c.pe
    @3
    @21
    polval2.o
    opoccl
    syl2anc
    ralrimiva
    #
    vx
    cA
    @12
    @4
    vp
    @7
    cX
    cK
    cM
    @21
    @7
    eqid
    #
    polval2.a
    polval2.m
    pmapglb2xN
    syldan
    @2
    @8
    @11
    cM
    @2
    @8
    @6
    @4
    c.pe
    cfv
    #
    wceq
    #
    vp
    cX
    wrex
    #
    vx
    cab
    #
    cU
    cfv
    #
    c.pe
    cfv
    #
    @11
    @0
    @1
    @14
    @8
    @30
    wceq
    @23
    vx
    @12
    @4
    cU
    vp
    @7
    cX
    cK
    c.pe
    @21
    polval2.u
    @24
    polval2.o
    glbconxN
    syldan
    @2
    @29
    @10
    c.pe
    @2
    @28
    cX
    cU
    @2
    @28
    vx
    vp
    weq
    #
    vp
    cX
    wrex
    #
    vx
    cab
    #
    cX
    @2
    @27
    @32
    vx
    @2
    @26
    @31
    vp
    cX
    @16
    @25
    @3
    @6
    @16
    @17
    @18
    @25
    @3
    wceq
    @19
    @22
    @12
    cK
    c.pe
    @3
    @21
    polval2.o
    opococ
    syl2anc
    eqeq2d
    rexbidva
    abbidv
    @33
    @6
    cX
    wcel
    #
    vx
    cab
    cX
    @32
    @34
    vx
    @32
    @15
    @31
    wa
    #
    vp
    wex
    vp
    vx
    weq
    #
    @15
    wa
    #
    vp
    wex
    @34
    @31
    vp
    cX
    df-rex
    @35
    @37
    vp
    @35
    @15
    @36
    wa
    @37
    @31
    @36
    @15
    vx
    vp
    equcom
    anbi2i
    @15
    @36
    ancom
    bitri
    exbii
    @15
    @34
    vp
    @6
    vx
    vex
    @3
    @6
    cX
    eleq1
    ceqsexv
    3bitri
    abbii
    vx
    cX
    abid2
    eqtri
    syl6eq
    fveq2d
    fveq2d
    eqtrd
    fveq2d
    3eqtr2d
end
