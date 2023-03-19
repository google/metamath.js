include "crn.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cocv.mm"
include "cfv.mm"
include "wceq.mm"
include "cvv.mm"
include "wb.mm"
include "chlh.mm"
include "fvex.mm"
include "eqeltri.mm"
include "eqid.mm"
include "iscss.mm"
include "mp1i.mm"
include "biimpa.mm"
include "cbs.mm"
include "wss.mm"
include "cssss.mm"
include "coch.mm"
include "cdvh.mm"
include "chlt.mm"
include "adantr.mm"
include "hlhilbase.mm"
include "sseq2d.mm"
include "biimpar.mm"
include "dochoccl.mm"
include "eqcom.mm"
include "hlhilocv.mm"
include "fveq2d.mm"
include "dochssv.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "eqeq1d.mm"
include "syl5bb.mm"
include "bitr4d.mm"
include "sylan2.mm"
include "mpbird.mm"
include "simpr.mm"
include "dihrnss.mm"
include "sylan.mm"
include "eqcomd.mm"
include "ex.mm"
include "3imtr4d.mm"
include "mpd.mm"
include "impbida.mm"
include "eqrdv.mm"

theorem hlhillcs
  let wph: wff ph
  let cC: class C
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let vx: setvar x
  assume hlhillcs.h: |- H = ( LHyp ` K )
  assume hlhillcs.i: |- I = ( ( DIsoH ` K ) ` W )
  assume hlhillcs.u: |- U = ( ( HLHil ` K ) ` W )
  assume hlhillcs.c: |- C = ( CSubSp ` U )
  assume hlhillcs.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> C = ran I )

  proof
    wph
    vx
    cC
    cI
    crn
    #
    wph
    vx
    cv
    #
    cC
    wcel
    #
    @1
    @0
    wcel
    #
    wph
    @2
    wa
    @3
    @1
    @1
    cU
    cocv
    cfv
    #
    cfv
    #
    @4
    cfv
    #
    wceq
    #
    wph
    @2
    @7
    cU
    cvv
    wcel
    #
    @2
    @7
    wb
    #
    wph
    cU
    cW
    cK
    chlh
    cfv
    #
    cfv
    cvv
    hlhillcs.u
    cW
    @10
    fvex
    eqeltri
    #
    cC
    @1
    @4
    cU
    cvv
    @4
    eqid
    #
    hlhillcs.c
    iscss
    #
    mp1i
    biimpa
    @2
    wph
    @1
    cU
    cbs
    cfv
    #
    wss
    #
    @3
    @7
    wb
    cC
    @1
    @14
    cU
    @14
    eqid
    hlhillcs.c
    cssss
    wph
    @15
    wa
    #
    @3
    @1
    cW
    cK
    coch
    cfv
    cfv
    #
    cfv
    #
    @17
    cfv
    #
    @1
    wceq
    #
    @7
    @16
    cW
    cK
    cdvh
    cfv
    cfv
    #
    cH
    cI
    cK
    @17
    @21
    cbs
    cfv
    #
    cW
    @1
    hlhillcs.h
    hlhillcs.i
    @21
    eqid
    #
    @22
    eqid
    #
    @17
    eqid
    #
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    @15
    hlhillcs.k
    adantr
    #
    wph
    @1
    @22
    wss
    #
    @15
    wph
    @22
    @14
    @1
    wph
    cU
    cH
    cK
    @21
    @22
    cW
    hlhillcs.h
    hlhillcs.u
    hlhillcs.k
    @23
    @24
    hlhilbase
    sseq2d
    biimpar
    #
    dochoccl
    @7
    @6
    @1
    wceq
    #
    @16
    @20
    @1
    @6
    eqcom
    @16
    @6
    @19
    @1
    @16
    @6
    @18
    @4
    cfv
    #
    @19
    @16
    @5
    @18
    @4
    @16
    cU
    cH
    cK
    @21
    @17
    @4
    @22
    cW
    @1
    hlhillcs.h
    @23
    hlhillcs.u
    @27
    @24
    @25
    @12
    @29
    hlhilocv
    fveq2d
    @16
    cU
    cH
    cK
    @21
    @17
    @4
    @22
    cW
    @18
    hlhillcs.h
    @23
    hlhillcs.u
    @27
    @24
    @25
    @12
    @16
    @26
    @28
    @18
    @22
    wss
    #
    @27
    @29
    @21
    cH
    cK
    @17
    @22
    cW
    @1
    hlhillcs.h
    @23
    @24
    @25
    dochssv
    #
    syl2anc
    hlhilocv
    eqtrd
    eqeq1d
    syl5bb
    bitr4d
    sylan2
    mpbird
    wph
    @3
    wa
    #
    @3
    @2
    wph
    @3
    simpr
    @34
    @20
    @7
    @3
    @2
    @34
    @20
    @7
    @34
    @20
    wa
    @6
    @1
    @34
    @30
    @20
    @34
    @6
    @19
    @1
    @34
    @6
    @31
    @19
    @34
    @5
    @18
    @4
    @34
    cU
    cH
    cK
    @21
    @17
    @4
    @22
    cW
    @1
    hlhillcs.h
    @23
    hlhillcs.u
    wph
    @26
    @3
    hlhillcs.k
    adantr
    #
    @24
    @25
    @12
    wph
    @26
    @3
    @28
    hlhillcs.k
    @21
    cH
    cI
    cK
    @22
    cW
    @1
    hlhillcs.h
    @23
    hlhillcs.i
    @24
    dihrnss
    sylan
    #
    hlhilocv
    fveq2d
    @34
    cU
    cH
    cK
    @21
    @17
    @4
    @22
    cW
    @18
    hlhillcs.h
    @23
    hlhillcs.u
    @35
    @24
    @25
    @12
    @34
    @26
    @28
    @32
    @35
    @36
    @33
    syl2anc
    hlhilocv
    eqtrd
    eqeq1d
    biimpar
    eqcomd
    ex
    @34
    @21
    cH
    cI
    cK
    @17
    @22
    cW
    @1
    hlhillcs.h
    hlhillcs.i
    @23
    @24
    @25
    @35
    @36
    dochoccl
    @8
    @9
    @34
    @11
    @13
    mp1i
    3imtr4d
    mpd
    impbida
    eqrdv
end
