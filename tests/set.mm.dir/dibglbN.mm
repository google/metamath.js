include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "cbs.mm"
include "crab.mm"
include "ciin.mm"
include "wceq.mm"
include "simpl.mm"
include "simprl.mm"
include "wb.mm"
include "eqid.mm"
include "dibdmN.mm"
include "sseq2d.mm"
include "adantr.mm"
include "mpbid.mm"
include "simprr.mm"
include "wrel.mm"
include "dibvalrel.mm"
include "wrex.mm"
include "wex.mm"
include "n0.mm"
include "biimpi.mm"
include "ad2antll.mm"
include "a1d.mm"
include "ancld.mm"
include "eximdv.mm"
include "mpd.mm"
include "df-rex.mm"
include "sylibr.mm"
include "reliin.mm"
include "syl.mm"
include "id.mm"
include "cdia.mm"
include "cltrn.mm"
include "cid.mm"
include "cres.mm"
include "cmpt.mm"
include "wral.mm"
include "cop.mm"
include "diadm.mm"
include "sseqtr4d.mm"
include "diaglbN.mm"
include "syl12anc.mm"
include "eleq2d.mm"
include "cvv.mm"
include "vex.mm"
include "eliin.mm"
include "ax-mp.mm"
include "syl6bb.mm"
include "anbi1d.mm"
include "r19.27zv.mm"
include "bitr4d.mm"
include "ccla.mm"
include "hlclat.mm"
include "ad2antrr.mm"
include "ssrab2.mm"
include "syl6ss.mm"
include "clatglbcl.mm"
include "syl2anc.mm"
include "clat.mm"
include "hllat.mm"
include "ad3antrrr.mm"
include "simplrl.mm"
include "sselda.mm"
include "lhpbase.mm"
include "ad3antlr.mm"
include "simpr.mm"
include "clatglble.mm"
include "syl3anc.mm"
include "breq1.mm"
include "elrab.mm"
include "sylib.mm"
include "simprd.mm"
include "lattrd.mm"
include "exlimddv.mm"
include "dibopelval2.mm"
include "opex.mm"
include "simpll.mm"
include "ralbidva.mm"
include "syl5bb.mm"
include "3bitr4d.mm"
include "eqrelrdv2.mm"
include "syl21anc.mm"

theorem dibglbN
  let vx: setvar x
  let cS: class S
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let vf: setvar f
  let vs: setvar s
  let vh: setvar h
  let vy: setvar y
  assume dibglb.g: |- G = ( glb ` K )
  assume dibglb.h: |- H = ( LHyp ` K )
  assume dibglb.i: |- I = ( ( DIsoB ` K ) ` W )

  disjoint G x
  disjoint H x
  disjoint K x
  disjoint S x
  disjoint W x
  disjoint f s
  disjoint f x
  disjoint G f
  disjoint s x
  disjoint G s
  disjoint H f
  disjoint H s
  disjoint I f
  disjoint I s
  disjoint f h
  disjoint f y
  disjoint K f
  disjoint h s
  disjoint h x
  disjoint h y
  disjoint K h
  disjoint s y
  disjoint K s
  disjoint x y
  disjoint K y
  disjoint S f
  disjoint S s
  disjoint W f
  disjoint W h
  disjoint W s
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
    @2
    cS
    vy
    cv
    #
    cW
    cK
    cple
    cfv
    #
    wbr
    #
    vy
    cK
    cbs
    cfv
    #
    crab
    #
    wss
    #
    @5
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
    wceq
    #
    @2
    @6
    simpl
    @7
    @4
    @13
    @2
    @4
    @5
    simprl
    @2
    @4
    @13
    wb
    @6
    @2
    @3
    @12
    cS
    vy
    @11
    cH
    cI
    cK
    @9
    chlt
    cW
    @11
    eqid
    #
    @9
    eqid
    #
    dibglb.h
    dibglb.i
    dibdmN
    sseq2d
    adantr
    mpbid
    @2
    @4
    @5
    simprr
    @2
    @13
    @5
    wa
    #
    wa
    #
    @15
    wrel
    #
    @18
    wrel
    #
    @23
    @19
    @2
    @24
    @22
    cH
    cI
    cK
    chlt
    cW
    @14
    dibglb.h
    dibglb.i
    dibvalrel
    adantr
    @23
    @17
    wrel
    #
    vx
    cS
    wrex
    #
    @25
    @23
    @16
    cS
    wcel
    #
    @26
    wa
    #
    vx
    wex
    #
    @27
    @23
    @28
    vx
    wex
    #
    @30
    @5
    @31
    @2
    @13
    @5
    @31
    vx
    cS
    n0
    biimpi
    ad2antll
    #
    @23
    @28
    @29
    vx
    @23
    @28
    @26
    @23
    @26
    @28
    @2
    @26
    @22
    cH
    cI
    cK
    chlt
    cW
    @16
    dibglb.h
    dibglb.i
    dibvalrel
    adantr
    a1d
    ancld
    eximdv
    mpd
    @26
    vx
    cS
    df-rex
    sylibr
    vx
    cS
    @17
    reliin
    syl
    @23
    id
    @23
    vf
    vs
    @15
    @18
    @23
    vf
    cv
    #
    @14
    cW
    cK
    cdia
    cfv
    cfv
    #
    cfv
    #
    wcel
    #
    vs
    cv
    #
    vh
    cW
    cK
    cltrn
    cfv
    cfv
    #
    cid
    @11
    cres
    cmpt
    #
    wceq
    #
    wa
    #
    @33
    @16
    @34
    cfv
    #
    wcel
    #
    @40
    wa
    #
    vx
    cS
    wral
    #
    @33
    @37
    cop
    #
    @15
    wcel
    #
    @46
    @18
    wcel
    #
    @23
    @41
    @43
    vx
    cS
    wral
    #
    @40
    wa
    #
    @45
    @23
    @36
    @49
    @40
    @23
    @36
    @33
    vx
    cS
    @42
    ciin
    #
    wcel
    #
    @49
    @23
    @35
    @51
    @33
    @23
    @2
    cS
    @34
    cdm
    #
    wss
    @5
    @35
    @51
    wceq
    @2
    @22
    simpl
    #
    @23
    cS
    @12
    @53
    @2
    @13
    @5
    simprl
    #
    @2
    @53
    @12
    wceq
    @22
    vy
    @11
    cH
    @34
    cK
    @9
    chlt
    cW
    @20
    @21
    dibglb.h
    @34
    eqid
    #
    diadm
    adantr
    sseqtr4d
    @2
    @13
    @5
    simprr
    vx
    cS
    cG
    cH
    @34
    cK
    cW
    dibglb.g
    dibglb.h
    @56
    diaglbN
    syl12anc
    eleq2d
    @33
    cvv
    wcel
    @52
    @49
    wb
    vf
    vex
    vx
    @33
    cS
    @42
    cvv
    eliin
    ax-mp
    syl6bb
    anbi1d
    @5
    @45
    @50
    wb
    @2
    @13
    @43
    @40
    vx
    cS
    r19.27zv
    ad2antll
    bitr4d
    @23
    @2
    @14
    @11
    wcel
    #
    @14
    cW
    @9
    wbr
    #
    @47
    @41
    wb
    @54
    @23
    cK
    ccla
    wcel
    #
    cS
    @11
    wss
    #
    @57
    @0
    @59
    @1
    @22
    cK
    hlclat
    #
    ad2antrr
    @23
    cS
    @12
    @11
    @55
    @10
    vy
    @11
    ssrab2
    #
    syl6ss
    #
    @11
    cS
    cG
    cK
    @20
    dibglb.g
    clatglbcl
    #
    syl2anc
    @23
    @28
    @58
    vx
    @32
    @23
    @28
    wa
    #
    @11
    cK
    @9
    @14
    @16
    cW
    @20
    @21
    @0
    cK
    clat
    wcel
    @1
    @22
    @28
    cK
    hllat
    ad3antrrr
    @65
    @59
    @60
    @57
    @0
    @59
    @1
    @22
    @28
    @61
    ad3antrrr
    #
    @65
    cS
    @12
    @11
    @2
    @13
    @5
    @28
    simplrl
    @62
    syl6ss
    #
    @64
    syl2anc
    @23
    cS
    @11
    @16
    @63
    sselda
    @1
    cW
    @11
    wcel
    @0
    @22
    @28
    @11
    cH
    cK
    cW
    @20
    dibglb.h
    lhpbase
    ad3antlr
    @65
    @59
    @60
    @28
    @14
    @16
    @9
    wbr
    @66
    @67
    @23
    @28
    simpr
    @11
    cS
    cG
    cK
    @9
    @16
    @20
    @21
    dibglb.g
    clatglble
    syl3anc
    @65
    @16
    @11
    wcel
    #
    @16
    cW
    @9
    wbr
    #
    @65
    @16
    @12
    wcel
    @68
    @69
    wa
    #
    @23
    cS
    @12
    @16
    @55
    sselda
    @10
    @69
    vy
    @16
    @11
    @8
    @16
    cW
    @9
    breq1
    elrab
    sylib
    #
    simprd
    lattrd
    exlimddv
    @11
    @37
    @38
    vh
    @33
    cH
    cI
    @34
    cK
    @9
    chlt
    cW
    @14
    @39
    @20
    @21
    dibglb.h
    @38
    eqid
    #
    @39
    eqid
    #
    @56
    dibglb.i
    dibopelval2
    syl12anc
    @48
    @46
    @17
    wcel
    #
    vx
    cS
    wral
    #
    @23
    @45
    @46
    cvv
    wcel
    @48
    @75
    wb
    @33
    @37
    opex
    vx
    @46
    cS
    @17
    cvv
    eliin
    ax-mp
    @23
    @74
    @44
    vx
    cS
    @65
    @2
    @70
    @74
    @44
    wb
    @2
    @22
    @28
    simpll
    @71
    @11
    @37
    @38
    vh
    @33
    cH
    cI
    @34
    cK
    @9
    chlt
    cW
    @16
    @39
    @20
    @21
    dibglb.h
    @72
    @73
    @56
    dibglb.i
    dibopelval2
    syl2anc
    ralbidva
    syl5bb
    3bitr4d
    eqrelrdv2
    syl21anc
    syl12anc
end
