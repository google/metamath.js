include "chlt.mm"
include "wcel.mm"
include "wral.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cfv.mm"
include "cple.mm"
include "wbr.mm"
include "catm.mm"
include "crab.mm"
include "ciin.mm"
include "wa.mm"
include "ccla.mm"
include "wss.mm"
include "wb.mm"
include "hlclat.mm"
include "ad2antrr.mm"
include "eqid.mm"
include "atbase.mm"
include "adantl.mm"
include "wi.mm"
include "r19.29.mm"
include "eleq1a.mm"
include "imp.mm"
include "rexlimivw.mm"
include "syl.mm"
include "ex.mm"
include "ad2antlr.mm"
include "abssdv.mm"
include "clatleglb.mm"
include "syl3anc.mm"
include "wal.mm"
include "vex.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elab.mm"
include "imbi1i.mm"
include "r19.23v.mm"
include "bitr4i.mm"
include "albii.mm"
include "df-ral.mm"
include "ralcom4.mm"
include "3bitr4i.mm"
include "nfv.mm"
include "breq2.mm"
include "ceqsalg.mm"
include "ralimi.mm"
include "ralbi.mm"
include "syl5bb.mm"
include "bitrd.mm"
include "rabbidva.mm"
include "3adant3.mm"
include "simp1.mm"
include "clatglbcl.mm"
include "syl2an.mm"
include "pmapval.mm"
include "syl2anc.mm"
include "iinrab.mm"
include "3ad2ant3.mm"
include "3eqtr4d.mm"
include "nfra1.mm"
include "nf3an.mm"
include "simpl1.mm"
include "rspa.mm"
include "3ad2antl2.mm"
include "iineq2d.mm"
include "eqtr4d.mm"

theorem pmapglbx
  let vy: setvar y
  let cB: class B
  let cS: class S
  let vi: setvar i
  let cG: class G
  let cI: class I
  let cK: class K
  let cM: class M
  let vp: setvar p
  let vx: setvar x
  let vz: setvar z
  assume pmapglb.b: |- B = ( Base ` K )
  assume pmapglb.g: |- G = ( glb ` K )
  assume pmapglb.m: |- M = ( pmap ` K )

  disjoint i y
  disjoint B i
  disjoint B y
  disjoint I i
  disjoint I y
  disjoint K i
  disjoint K y
  disjoint S y
  disjoint i p
  disjoint i x
  disjoint i z
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint B p
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B z
  disjoint G p
  disjoint G z
  disjoint I p
  disjoint I z
  disjoint K p
  disjoint K x
  disjoint K z
  disjoint S p
  disjoint S x
  disjoint S z
  assert |- ( ( K e. HL /\ A. i e. I S e. B /\ I =/= (/) ) -> ( M ` ( G ` { y | E. i e. I y = S } ) ) = |^|_ i e. I ( M ` S ) )

  proof
    cK
    chlt
    wcel
    #
    cS
    cB
    wcel
    #
    vi
    cI
    wral
    #
    cI
    c0
    wne
    #
    w3a
    #
    vy
    cv
    #
    cS
    wceq
    #
    vi
    cI
    wrex
    #
    vy
    cab
    #
    cG
    cfv
    #
    cM
    cfv
    #
    vi
    cI
    vp
    cv
    #
    cS
    cK
    cple
    cfv
    #
    wbr
    #
    vp
    cK
    catm
    cfv
    #
    crab
    #
    ciin
    #
    vi
    cI
    cS
    cM
    cfv
    #
    ciin
    @4
    @11
    @9
    @12
    wbr
    #
    vp
    @14
    crab
    #
    @13
    vi
    cI
    wral
    #
    vp
    @14
    crab
    #
    @10
    @16
    @0
    @2
    @19
    @21
    wceq
    @3
    @0
    @2
    wa
    #
    @18
    @20
    vp
    @14
    @22
    @11
    @14
    wcel
    #
    wa
    #
    @18
    @11
    vz
    cv
    #
    @12
    wbr
    #
    vz
    @8
    wral
    #
    @20
    @24
    cK
    ccla
    wcel
    #
    @11
    cB
    wcel
    #
    @8
    cB
    wss
    #
    @18
    @27
    wb
    @0
    @28
    @2
    @23
    cK
    hlclat
    #
    ad2antrr
    @23
    @29
    @22
    @14
    cB
    @11
    cK
    pmapglb.b
    @14
    eqid
    #
    atbase
    adantl
    @24
    @7
    vy
    cB
    @2
    @7
    @5
    cB
    wcel
    #
    wi
    @0
    @23
    @2
    @7
    @33
    @2
    @7
    wa
    @1
    @6
    wa
    #
    vi
    cI
    wrex
    @33
    @1
    @6
    vi
    cI
    r19.29
    @34
    @33
    vi
    cI
    @1
    @6
    @33
    cS
    cB
    @5
    eleq1a
    imp
    rexlimivw
    syl
    ex
    #
    ad2antlr
    abssdv
    vz
    cB
    @8
    cG
    cK
    @12
    @11
    pmapglb.b
    @12
    eqid
    #
    pmapglb.g
    clatleglb
    syl3anc
    @2
    @27
    @20
    wb
    @0
    @23
    @27
    @25
    cS
    wceq
    #
    @26
    wi
    #
    vz
    wal
    #
    vi
    cI
    wral
    #
    @2
    @20
    @25
    @8
    wcel
    #
    @26
    wi
    #
    vz
    wal
    @38
    vi
    cI
    wral
    #
    vz
    wal
    @27
    @40
    @42
    @43
    vz
    @42
    @37
    vi
    cI
    wrex
    #
    @26
    wi
    @43
    @41
    @44
    @26
    @7
    @44
    vy
    @25
    vz
    vex
    @5
    @25
    wceq
    @6
    @37
    vi
    cI
    @5
    @25
    cS
    eqeq1
    rexbidv
    elab
    imbi1i
    @37
    @26
    vi
    cI
    r19.23v
    bitr4i
    albii
    @26
    vz
    @8
    df-ral
    @38
    vi
    vz
    cI
    ralcom4
    3bitr4i
    @2
    @39
    @13
    wb
    #
    vi
    cI
    wral
    @40
    @20
    wb
    @1
    @45
    vi
    cI
    @26
    @13
    vz
    cS
    cB
    @13
    vz
    nfv
    @25
    cS
    @11
    @12
    breq2
    ceqsalg
    ralimi
    @39
    @13
    vi
    cI
    ralbi
    syl
    syl5bb
    ad2antlr
    bitrd
    rabbidva
    3adant3
    @4
    @0
    @9
    cB
    wcel
    #
    @10
    @19
    wceq
    @0
    @2
    @3
    simp1
    @0
    @2
    @46
    @3
    @0
    @28
    @30
    @46
    @2
    @31
    @2
    @7
    vy
    cB
    @35
    abssdv
    cB
    @8
    cG
    cK
    pmapglb.b
    pmapglb.g
    clatglbcl
    syl2an
    3adant3
    @14
    cB
    chlt
    cK
    @12
    cM
    @9
    vp
    pmapglb.b
    @36
    @32
    pmapglb.m
    pmapval
    syl2anc
    @3
    @0
    @16
    @21
    wceq
    @2
    @13
    vi
    vp
    cI
    @14
    iinrab
    3ad2ant3
    3eqtr4d
    @4
    vi
    cI
    @17
    @15
    @0
    @2
    @3
    vi
    @0
    vi
    nfv
    @1
    vi
    cI
    nfra1
    @3
    vi
    nfv
    nf3an
    @4
    vi
    cv
    cI
    wcel
    #
    wa
    @0
    @1
    @17
    @15
    wceq
    @0
    @2
    @3
    @47
    simpl1
    @2
    @0
    @47
    @1
    @3
    @1
    vi
    cI
    rspa
    3ad2antl2
    @14
    cB
    chlt
    cK
    @12
    cM
    cS
    vp
    pmapglb.b
    @36
    @32
    pmapglb.m
    pmapval
    syl2anc
    iineq2d
    eqtr4d
end
