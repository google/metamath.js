include "csn.mm"
include "cfv.mm"
include "cv.mm"
include "clk.mm"
include "coch.mm"
include "wceq.mm"
include "wss.mm"
include "wa.mm"
include "clfn.mm"
include "crab.mm"
include "clss.mm"
include "chlt.mm"
include "eqid.mm"
include "clmod.mm"
include "wcel.mm"
include "dvhlmod.mm"
include "lsssn0.mm"
include "syl.mm"
include "mapdval.mm"
include "cbs.mm"
include "csca.mm"
include "c0g.mm"
include "cxp.mm"
include "simprrr.mm"
include "wb.mm"
include "adantr.mm"
include "simprl.mm"
include "lkrssv.mm"
include "dochlss.mm"
include "syl2anc.mm"
include "lssle0.mm"
include "mpbid.mm"
include "fveq2d.mm"
include "simprrl.mm"
include "doch0.mm"
include "3eqtr3d.mm"
include "lkr0f.mm"
include "lcd0v.mm"
include "eqtr4d.mm"
include "ex.mm"
include "lcd0vcl.mm"
include "lcdvbaselfl.mm"
include "mpbird.mm"
include "dochoc1.mm"
include "eqtrd.mm"
include "doch1.mm"
include "eqimss.mm"
include "jca32.mm"
include "eleq1.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "syl5ibrcom.mm"
include "impbid.mm"
include "weq.mm"
include "elrab.mm"
include "velsn.mm"
include "3bitr4g.mm"
include "eqrdv.mm"

theorem mapd0
  let wph: wff ph
  let cC: class C
  let cU: class U
  let cH: class H
  let cK: class K
  let cM: class M
  let cO: class O
  let cW: class W
  let c.0: class .0.
  let vf: setvar f
  let vg: setvar g
  assume mapd0.h: |- H = ( LHyp ` K )
  assume mapd0.m: |- M = ( ( mapd ` K ) ` W )
  assume mapd0.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapd0.o: |- O = ( 0g ` U )
  assume mapd0.c: |- C = ( ( LCDual ` K ) ` W )
  assume mapd0.z: |- .0. = ( 0g ` C )
  assume mapd0.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> ( M ` { O } ) = { .0. } )

  proof
    wph
    cO
    csn
    #
    cM
    cfv
    vf
    cv
    #
    cU
    clk
    cfv
    #
    cfv
    #
    cW
    cK
    coch
    cfv
    cfv
    #
    cfv
    #
    @4
    cfv
    #
    @3
    wceq
    #
    @5
    @0
    wss
    #
    wa
    #
    vf
    cU
    clfn
    cfv
    #
    crab
    #
    c.0
    csn
    #
    wph
    cU
    clss
    cfv
    #
    @0
    cU
    vf
    @10
    cH
    cK
    @2
    cM
    @4
    cW
    chlt
    mapd0.h
    mapd0.u
    @13
    eqid
    #
    @10
    eqid
    #
    @2
    eqid
    #
    @4
    eqid
    #
    mapd0.m
    mapd0.k
    wph
    cU
    clmod
    wcel
    #
    @0
    @13
    wcel
    wph
    cU
    cH
    cK
    cW
    mapd0.h
    mapd0.u
    mapd0.k
    dvhlmod
    #
    @13
    cU
    cO
    mapd0.o
    @14
    lsssn0
    syl
    mapdval
    wph
    vg
    @11
    @12
    wph
    vg
    cv
    #
    @10
    wcel
    #
    @20
    @2
    cfv
    #
    @4
    cfv
    #
    @4
    cfv
    #
    @22
    wceq
    #
    @23
    @0
    wss
    #
    wa
    #
    wa
    #
    @20
    c.0
    wceq
    #
    @20
    @11
    wcel
    @20
    @12
    wcel
    wph
    @28
    @29
    wph
    @28
    @29
    wph
    @28
    wa
    #
    @20
    cU
    cbs
    cfv
    #
    cU
    csca
    cfv
    #
    c0g
    cfv
    #
    csn
    cxp
    #
    c.0
    @30
    @22
    @31
    wceq
    #
    @20
    @34
    wceq
    #
    @30
    @24
    @0
    @4
    cfv
    #
    @22
    @31
    @30
    @23
    @0
    @4
    @30
    @26
    @23
    @0
    wceq
    #
    wph
    @21
    @25
    @26
    simprrr
    @30
    @18
    @23
    @13
    wcel
    #
    @26
    @38
    wb
    wph
    @18
    @28
    @19
    adantr
    #
    @30
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @22
    @31
    wss
    @39
    wph
    @41
    @28
    mapd0.k
    adantr
    @30
    @10
    @20
    @2
    @31
    cU
    @31
    eqid
    #
    @15
    @16
    @40
    wph
    @21
    @27
    simprl
    #
    lkrssv
    @13
    cU
    cH
    cK
    @4
    @31
    cW
    @22
    mapd0.h
    mapd0.u
    @42
    @14
    @17
    dochlss
    syl2anc
    @13
    cU
    @23
    cO
    mapd0.o
    @14
    lssle0
    syl2anc
    mpbid
    fveq2d
    wph
    @21
    @25
    @26
    simprrl
    wph
    @37
    @31
    wceq
    #
    @28
    wph
    @41
    @44
    mapd0.k
    cU
    cH
    cK
    @4
    @31
    cW
    cO
    mapd0.h
    mapd0.u
    @17
    @42
    mapd0.o
    doch0
    syl
    adantr
    3eqtr3d
    @30
    @18
    @21
    @35
    @36
    wb
    @40
    @43
    @32
    @10
    @20
    @2
    @31
    cU
    @33
    @32
    eqid
    #
    @33
    eqid
    #
    @42
    @15
    @16
    lkr0f
    syl2anc
    mpbid
    wph
    c.0
    @34
    wceq
    #
    @28
    wph
    cC
    @32
    cU
    cH
    cK
    c.0
    @31
    cW
    @33
    mapd0.h
    mapd0.u
    @42
    @45
    @46
    mapd0.c
    mapd0.z
    mapd0.k
    lcd0v
    #
    adantr
    eqtr4d
    ex
    wph
    @28
    @29
    c.0
    @10
    wcel
    #
    c.0
    @2
    cfv
    #
    @4
    cfv
    #
    @4
    cfv
    #
    @50
    wceq
    #
    @51
    @0
    wss
    #
    wa
    #
    wa
    wph
    @49
    @53
    @54
    wph
    cC
    cU
    @10
    cH
    cK
    cC
    cbs
    cfv
    #
    cW
    c.0
    mapd0.h
    mapd0.c
    @56
    eqid
    #
    mapd0.u
    @15
    mapd0.k
    wph
    cC
    cH
    cK
    c.0
    @56
    cW
    mapd0.h
    mapd0.c
    @57
    mapd0.z
    mapd0.k
    lcd0vcl
    lcdvbaselfl
    #
    wph
    @52
    @31
    @50
    wph
    @52
    @31
    @4
    cfv
    #
    @4
    cfv
    @31
    wph
    @51
    @59
    @4
    wph
    @50
    @31
    @4
    wph
    @50
    @31
    wceq
    #
    @47
    @48
    wph
    @18
    @49
    @60
    @47
    wb
    @19
    @58
    @32
    @10
    c.0
    @2
    @31
    cU
    @33
    @45
    @46
    @42
    @15
    @16
    lkr0f
    syl2anc
    mpbird
    #
    fveq2d
    #
    fveq2d
    wph
    cU
    cH
    cK
    @4
    @31
    cW
    mapd0.h
    mapd0.u
    @17
    @42
    mapd0.k
    dochoc1
    eqtrd
    @61
    eqtr4d
    wph
    @51
    @0
    wceq
    @54
    wph
    @51
    @59
    @0
    @62
    wph
    @41
    @59
    @0
    wceq
    mapd0.k
    cU
    cH
    cK
    @4
    @31
    cW
    cO
    mapd0.h
    mapd0.u
    @17
    @42
    mapd0.o
    doch1
    syl
    eqtrd
    @51
    @0
    eqimss
    syl
    jca32
    @29
    @21
    @49
    @27
    @55
    @20
    c.0
    @10
    eleq1
    @29
    @25
    @53
    @26
    @54
    @29
    @24
    @52
    @22
    @50
    @29
    @23
    @51
    @4
    @29
    @22
    @50
    @4
    @20
    c.0
    @2
    fveq2
    #
    fveq2d
    #
    fveq2d
    @63
    eqeq12d
    @29
    @23
    @51
    @0
    @64
    sseq1d
    anbi12d
    anbi12d
    syl5ibrcom
    impbid
    @9
    @27
    vf
    @20
    @10
    vf
    vg
    weq
    #
    @7
    @25
    @8
    @26
    @65
    @6
    @24
    @3
    @22
    @65
    @5
    @23
    @4
    @65
    @3
    @22
    @4
    @1
    @20
    @2
    fveq2
    #
    fveq2d
    #
    fveq2d
    @66
    eqeq12d
    @65
    @5
    @23
    @0
    @67
    sseq1d
    anbi12d
    elrab
    vg
    c.0
    velsn
    3bitr4g
    eqrdv
    eqtrd
end
