include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cv.mm"
include "cfv.mm"
include "crab.mm"
include "ciin.mm"
include "crn.mm"
include "cint.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "simpl.mm"
include "ssrab2.mm"
include "a1i.mm"
include "cp1.mm"
include "cops.mm"
include "hlop.mm"
include "ad2antrr.mm"
include "eqid.mm"
include "op1cl.mm"
include "syl.mm"
include "simpr.mm"
include "dih1.mm"
include "adantr.mm"
include "sseqtr4d.mm"
include "fveq2.mm"
include "sseq2d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "ne0i.mm"
include "dihglb.mm"
include "syl12anc.mm"
include "wrex.mm"
include "cab.mm"
include "fvex.mm"
include "dfiin2.mm"
include "wex.mm"
include "wb.mm"
include "wfn.mm"
include "dihfn.mm"
include "fvelrnb.mm"
include "eqcom.mm"
include "rexbii.mm"
include "df-rex.mm"
include "bitri.mm"
include "syl6bb.mm"
include "ex.mm"
include "pm5.32rd.mm"
include "weq.mm"
include "anbi1i.mm"
include "sseq2.mm"
include "anbi2d.mm"
include "pm5.32ri.mm"
include "an32.mm"
include "3bitr2i.mm"
include "exbii.mm"
include "19.41v.mm"
include "3bitrri.mm"
include "syl6rbb.mm"
include "abbidv.mm"
include "df-rab.mm"
include "syl6eqr.mm"
include "inteqd.mm"
include "syl5eq.mm"
include "eqtrd.mm"

theorem dihglb2
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cS: class S
  let cU: class U
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let cV: class V
  let cW: class W
  let vz: setvar z
  assume dihglb.b: |- B = ( Base ` K )
  assume dihglb.g: |- G = ( glb ` K )
  assume dihglb.h: |- H = ( LHyp ` K )
  assume dihglb.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihglb2.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihglb2.v: |- V = ( Base ` U )

  disjoint B x
  disjoint I x
  disjoint K x
  disjoint S x
  disjoint x y
  disjoint B y
  disjoint H y
  disjoint I y
  disjoint K y
  disjoint S y
  disjoint V y
  disjoint W y
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint G z
  disjoint H z
  disjoint I z
  disjoint K z
  disjoint S z
  disjoint W z
  assert |- ( ( ( K e. HL /\ W e. H ) /\ S C_ V ) -> ( I ` ( G ` { x e. B | S C_ ( I ` x ) } ) ) = |^| { y e. ran I | S C_ y } )

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
    cS
    cV
    wss
    #
    wa
    #
    cS
    vx
    cv
    #
    cI
    cfv
    #
    wss
    #
    vx
    cB
    crab
    #
    cG
    cfv
    cI
    cfv
    #
    vz
    @8
    vz
    cv
    #
    cI
    cfv
    #
    ciin
    #
    cS
    vy
    cv
    #
    wss
    #
    vy
    cI
    crn
    #
    crab
    #
    cint
    #
    @4
    @2
    @8
    cB
    wss
    #
    @8
    c0
    wne
    #
    @9
    @12
    wceq
    @2
    @3
    simpl
    @18
    @4
    @7
    vx
    cB
    ssrab2
    a1i
    @4
    cK
    cp1
    cfv
    #
    @8
    wcel
    #
    @19
    @4
    @20
    cB
    wcel
    #
    cS
    @20
    cI
    cfv
    #
    wss
    #
    @21
    @4
    cK
    cops
    wcel
    #
    @22
    @0
    @25
    @1
    @3
    cK
    hlop
    ad2antrr
    cB
    @20
    cK
    dihglb.b
    @20
    eqid
    #
    op1cl
    syl
    @4
    cS
    cV
    @23
    @2
    @3
    simpr
    @2
    @23
    cV
    wceq
    @3
    cU
    @20
    cH
    cI
    cK
    cV
    cW
    @26
    dihglb.h
    dihglb.i
    dihglb2.u
    dihglb2.v
    dih1
    adantr
    sseqtr4d
    @7
    @24
    vx
    @20
    cB
    @5
    @20
    wceq
    @6
    @23
    cS
    @5
    @20
    cI
    fveq2
    sseq2d
    elrab
    sylanbrc
    @8
    @20
    ne0i
    syl
    vz
    cB
    @8
    cG
    cH
    cI
    cK
    cW
    dihglb.b
    dihglb.g
    dihglb.h
    dihglb.i
    dihglb
    syl12anc
    @4
    @12
    @13
    @11
    wceq
    #
    vz
    @8
    wrex
    #
    vy
    cab
    #
    cint
    @17
    vz
    vy
    @8
    @11
    @10
    cI
    fvex
    dfiin2
    @4
    @29
    @16
    @4
    @29
    @13
    @15
    wcel
    #
    @14
    wa
    #
    vy
    cab
    @16
    @4
    @28
    @31
    vy
    @4
    @31
    @10
    cB
    wcel
    #
    @27
    wa
    #
    vz
    wex
    #
    @14
    wa
    #
    @28
    @4
    @14
    @30
    @34
    @4
    @14
    @30
    @34
    wb
    @4
    @14
    wa
    #
    @30
    @11
    @13
    wceq
    #
    vz
    cB
    wrex
    #
    @34
    @36
    cI
    cB
    wfn
    #
    @30
    @38
    wb
    @2
    @39
    @3
    @14
    cB
    cH
    cI
    cK
    cW
    dihglb.b
    dihglb.h
    dihglb.i
    dihfn
    ad2antrr
    vz
    cB
    @13
    cI
    fvelrnb
    syl
    @38
    @27
    vz
    cB
    wrex
    @34
    @37
    @27
    vz
    cB
    @11
    @13
    eqcom
    rexbii
    @27
    vz
    cB
    df-rex
    bitri
    syl6bb
    ex
    pm5.32rd
    @28
    @10
    @8
    wcel
    #
    @27
    wa
    #
    vz
    wex
    @33
    @14
    wa
    #
    vz
    wex
    @35
    @27
    vz
    @8
    df-rex
    @41
    @42
    vz
    @41
    @32
    cS
    @11
    wss
    #
    wa
    #
    @27
    wa
    @32
    @14
    wa
    #
    @27
    wa
    @42
    @40
    @44
    @27
    @7
    @43
    vx
    @10
    cB
    vx
    vz
    weq
    @6
    @11
    cS
    @5
    @10
    cI
    fveq2
    sseq2d
    elrab
    anbi1i
    @27
    @45
    @44
    @27
    @14
    @43
    @32
    @13
    @11
    cS
    sseq2
    anbi2d
    pm5.32ri
    @32
    @14
    @27
    an32
    3bitr2i
    exbii
    @33
    @14
    vz
    19.41v
    3bitrri
    syl6rbb
    abbidv
    @14
    vy
    @15
    df-rab
    syl6eqr
    inteqd
    syl5eq
    eqtrd
end
