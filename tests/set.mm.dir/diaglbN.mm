include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "cv.mm"
include "ciin.mm"
include "cltrn.mm"
include "ctrl.mm"
include "cple.mm"
include "wbr.mm"
include "cbs.mm"
include "wb.mm"
include "simpl.mm"
include "ccla.mm"
include "hlclat.mm"
include "ad2antrr.mm"
include "crab.mm"
include "eqid.mm"
include "diadm.mm"
include "sseq2d.mm"
include "biimpa.mm"
include "adantrr.mm"
include "ssrab2.mm"
include "syl6ss.mm"
include "clatglbcl.mm"
include "syl2anc.mm"
include "wex.mm"
include "simprr.mm"
include "n0.mm"
include "sylib.mm"
include "clat.mm"
include "hllat.mm"
include "ad3antrrr.mm"
include "adantr.mm"
include "ssel2.mm"
include "adantlr.mm"
include "adantll.mm"
include "diaeldm.mm"
include "mpbid.mm"
include "simpld.mm"
include "lhpbase.mm"
include "ad3antlr.mm"
include "simpr.mm"
include "clatglble.mm"
include "syl3anc.mm"
include "simprd.mm"
include "lattrd.mm"
include "exlimddv.mm"
include "diaelval.mm"
include "syl12anc.mm"
include "wral.mm"
include "r19.28zv.mm"
include "ad2antll.mm"
include "simpll.mm"
include "ralbidva.mm"
include "trlcl.mm"
include "clatleglb.mm"
include "pm5.32da.mm"
include "3bitr4rd.mm"
include "cvv.mm"
include "vex.mm"
include "eliin.mm"
include "ax-mp.mm"
include "syl6bbr.mm"
include "bitrd.mm"
include "eqrdv.mm"

theorem diaglbN
  let vx: setvar x
  let cS: class S
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let vf: setvar f
  let vy: setvar y
  assume diaglb.g: |- G = ( glb ` K )
  assume diaglb.h: |- H = ( LHyp ` K )
  assume diaglb.i: |- I = ( ( DIsoA ` K ) ` W )

  disjoint G x
  disjoint H x
  disjoint I x
  disjoint K x
  disjoint S x
  disjoint W x
  disjoint f x
  disjoint G f
  disjoint H f
  disjoint I f
  disjoint f y
  disjoint K f
  disjoint x y
  disjoint K y
  disjoint S f
  disjoint W f
  disjoint W y
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( S C_ dom I /\ S =/= (/) ) ) -> ( I ` ( G ` S ) ) = |^|_ x e. S ( I ` x ) )

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
    cI
    cdm
    #
    wss
    #
    cS
    c0
    wne
    #
    wa
    #
    wa
    #
    vf
    cS
    cG
    cfv
    #
    cI
    cfv
    #
    vx
    cS
    vx
    cv
    #
    cI
    cfv
    #
    ciin
    #
    @7
    vf
    cv
    #
    @9
    wcel
    #
    @13
    cW
    cK
    cltrn
    cfv
    cfv
    #
    wcel
    #
    @13
    cW
    cK
    ctrl
    cfv
    cfv
    #
    cfv
    #
    @8
    cK
    cple
    cfv
    #
    wbr
    #
    wa
    #
    @13
    @12
    wcel
    #
    @7
    @2
    @8
    cK
    cbs
    cfv
    #
    wcel
    #
    @8
    cW
    @19
    wbr
    #
    @14
    @21
    wb
    @2
    @6
    simpl
    @7
    cK
    ccla
    wcel
    #
    cS
    @23
    wss
    #
    @24
    @0
    @26
    @1
    @6
    cK
    hlclat
    #
    ad2antrr
    @7
    cS
    vy
    cv
    cW
    @19
    wbr
    #
    vy
    @23
    crab
    #
    @23
    @2
    @4
    cS
    @30
    wss
    #
    @5
    @2
    @4
    @31
    @2
    @3
    @30
    cS
    vy
    @23
    cH
    cI
    cK
    @19
    chlt
    cW
    @23
    eqid
    #
    @19
    eqid
    #
    diaglb.h
    diaglb.i
    diadm
    sseq2d
    biimpa
    adantrr
    @29
    vy
    @23
    ssrab2
    syl6ss
    #
    @23
    cS
    cG
    cK
    @32
    diaglb.g
    clatglbcl
    syl2anc
    #
    @7
    @10
    cS
    wcel
    #
    @25
    vx
    @7
    @5
    @36
    vx
    wex
    @2
    @4
    @5
    simprr
    vx
    cS
    n0
    sylib
    @7
    @36
    wa
    #
    @23
    cK
    @19
    @8
    @10
    cW
    @32
    @33
    @0
    cK
    clat
    wcel
    @1
    @6
    @36
    cK
    hllat
    ad3antrrr
    @7
    @24
    @36
    @35
    adantr
    @37
    @10
    @23
    wcel
    #
    @10
    cW
    @19
    wbr
    #
    @37
    @10
    @3
    wcel
    #
    @38
    @39
    wa
    #
    @6
    @36
    @40
    @2
    @4
    @36
    @40
    @5
    cS
    @3
    @10
    ssel2
    adantlr
    adantll
    @2
    @40
    @41
    wb
    @6
    @36
    @23
    cH
    cI
    cK
    @19
    chlt
    cW
    @10
    @32
    @33
    diaglb.h
    diaglb.i
    diaeldm
    ad2antrr
    mpbid
    #
    simpld
    @1
    cW
    @23
    wcel
    @0
    @6
    @36
    @23
    cH
    cK
    cW
    @32
    diaglb.h
    lhpbase
    ad3antlr
    @37
    @26
    @27
    @36
    @8
    @10
    @19
    wbr
    @0
    @26
    @1
    @6
    @36
    @28
    ad3antrrr
    @7
    @27
    @36
    @34
    adantr
    @7
    @36
    simpr
    @23
    cS
    cG
    cK
    @19
    @10
    @32
    @33
    diaglb.g
    clatglble
    syl3anc
    @37
    @38
    @39
    @42
    simprd
    lattrd
    exlimddv
    @23
    @17
    @15
    @13
    cH
    cI
    cK
    @19
    chlt
    cW
    @8
    @32
    @33
    diaglb.h
    @15
    eqid
    #
    @17
    eqid
    #
    diaglb.i
    diaelval
    syl12anc
    @7
    @21
    @13
    @11
    wcel
    #
    vx
    cS
    wral
    #
    @22
    @7
    @16
    @18
    @10
    @19
    wbr
    #
    wa
    #
    vx
    cS
    wral
    #
    @16
    @47
    vx
    cS
    wral
    #
    wa
    #
    @46
    @21
    @5
    @49
    @51
    wb
    @2
    @4
    @16
    @47
    vx
    cS
    r19.28zv
    ad2antll
    @7
    @45
    @48
    vx
    cS
    @37
    @2
    @41
    @45
    @48
    wb
    @2
    @6
    @36
    simpll
    @42
    @23
    @17
    @15
    @13
    cH
    cI
    cK
    @19
    chlt
    cW
    @10
    @32
    @33
    diaglb.h
    @43
    @44
    diaglb.i
    diaelval
    syl2anc
    ralbidva
    @7
    @16
    @20
    @50
    @7
    @16
    wa
    @26
    @18
    @23
    wcel
    #
    @27
    @20
    @50
    wb
    @0
    @26
    @1
    @6
    @16
    @28
    ad3antrrr
    @2
    @16
    @52
    @6
    @23
    @17
    @15
    @13
    cH
    cK
    cW
    @32
    diaglb.h
    @43
    @44
    trlcl
    adantlr
    @7
    @27
    @16
    @34
    adantr
    vx
    @23
    cS
    cG
    cK
    @19
    @18
    @32
    @33
    diaglb.g
    clatleglb
    syl3anc
    pm5.32da
    3bitr4rd
    @13
    cvv
    wcel
    @22
    @46
    wb
    vf
    vex
    vx
    @13
    cS
    @11
    cvv
    eliin
    ax-mp
    syl6bbr
    bitrd
    eqrdv
end
