include "cfv.mm"
include "wpss.mm"
include "cv.mm"
include "wa.mm"
include "clss.mm"
include "wrex.mm"
include "wn.mm"
include "wbr.mm"
include "mapdsord.mm"
include "wcel.mm"
include "eqid.mm"
include "chlt.mm"
include "adantr.mm"
include "simpr.mm"
include "mapdcl2.mm"
include "ccnv.mm"
include "wceq.mm"
include "crn.mm"
include "mapdrn2.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "mapdcnvcl.mm"
include "mapdcnvid2.mm"
include "eqcomd.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "wb.mm"
include "psseq2.mm"
include "psseq1.mm"
include "anbi12d.mm"
include "adantl.mm"
include "rexxfrd.mm"
include "rexbidva.mm"
include "bitrd.mm"
include "notbid.mm"
include "clmod.mm"
include "lcdlmod.mm"
include "lcvbr.mm"
include "dvhlmod.mm"
include "3bitr4rd.mm"

theorem mapdcv
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cS: class S
  let cU: class U
  let cE: class E
  let cH: class H
  let cK: class K
  let cM: class M
  let cW: class W
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vv: setvar v
  assume mapdcv.h: |- H = ( LHyp ` K )
  assume mapdcv.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdcv.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdcv.s: |- S = ( LSubSp ` U )
  assume mapdcv.c: |- C = ( <oL ` U )
  assume mapdcv.d: |- D = ( ( LCDual ` K ) ` W )
  assume mapdcv.e: |- E = ( <oL ` D )
  assume mapdcv.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdcv.x: |- ( ph -> X e. S )
  assume mapdcv.y: |- ( ph -> Y e. S )


  assert |- ( ph -> ( X C Y <-> ( M ` X ) E ( M ` Y ) ) )

  proof
    wph
    cX
    cM
    cfv
    #
    cY
    cM
    cfv
    #
    wpss
    #
    @0
    vf
    cv
    #
    wpss
    #
    @3
    @1
    wpss
    #
    wa
    #
    vf
    cD
    clss
    cfv
    #
    wrex
    #
    wn
    #
    wa
    cX
    cY
    wpss
    #
    cX
    vv
    cv
    #
    wpss
    #
    @11
    cY
    wpss
    #
    wa
    #
    vv
    cS
    wrex
    #
    wn
    #
    wa
    @0
    @1
    cE
    wbr
    cX
    cY
    cC
    wbr
    wph
    @2
    @10
    @9
    @16
    wph
    cS
    cU
    cH
    cK
    cM
    cW
    cX
    cY
    mapdcv.h
    mapdcv.m
    mapdcv.u
    mapdcv.s
    mapdcv.k
    mapdcv.x
    mapdcv.y
    mapdsord
    wph
    @8
    @15
    wph
    @8
    @0
    @11
    cM
    cfv
    #
    wpss
    #
    @17
    @1
    wpss
    #
    wa
    #
    vv
    cS
    wrex
    @15
    wph
    @6
    @20
    vf
    vv
    @17
    @7
    cS
    wph
    @11
    cS
    wcel
    #
    wa
    #
    cD
    @11
    cS
    @7
    cU
    cH
    cK
    cM
    cW
    mapdcv.h
    mapdcv.m
    mapdcv.u
    mapdcv.s
    mapdcv.d
    @7
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
    @21
    mapdcv.k
    adantr
    #
    wph
    @21
    simpr
    #
    mapdcl2
    wph
    @3
    @7
    wcel
    #
    wa
    #
    @3
    cM
    ccnv
    cfv
    #
    cS
    wcel
    @3
    @29
    cM
    cfv
    #
    wceq
    #
    @3
    @17
    wceq
    #
    vv
    cS
    wrex
    @28
    cS
    cU
    cH
    cK
    cM
    cW
    @3
    mapdcv.h
    mapdcv.m
    mapdcv.u
    mapdcv.s
    wph
    @24
    @27
    mapdcv.k
    adantr
    #
    wph
    @3
    cM
    crn
    #
    wcel
    @27
    wph
    @34
    @7
    @3
    wph
    cD
    @7
    cH
    cK
    cM
    cW
    mapdcv.h
    mapdcv.m
    mapdcv.d
    @23
    mapdcv.k
    mapdrn2
    eleq2d
    biimpar
    #
    mapdcnvcl
    @28
    @30
    @3
    @28
    cH
    cK
    cM
    cW
    @3
    mapdcv.h
    mapdcv.m
    @33
    @35
    mapdcnvid2
    eqcomd
    @32
    @31
    vv
    @29
    cS
    @11
    @29
    wceq
    @17
    @30
    @3
    @11
    @29
    cM
    fveq2
    eqeq2d
    rspcev
    syl2anc
    @32
    @6
    @20
    wb
    wph
    @32
    @4
    @18
    @5
    @19
    @3
    @17
    @0
    psseq2
    @3
    @17
    @1
    psseq1
    anbi12d
    adantl
    rexxfrd
    wph
    @20
    @14
    vv
    cS
    @22
    @18
    @12
    @19
    @13
    @22
    cS
    cU
    cH
    cK
    cM
    cW
    cX
    @11
    mapdcv.h
    mapdcv.m
    mapdcv.u
    mapdcv.s
    @25
    wph
    cX
    cS
    wcel
    @21
    mapdcv.x
    adantr
    @26
    mapdsord
    @22
    cS
    cU
    cH
    cK
    cM
    cW
    @11
    cY
    mapdcv.h
    mapdcv.m
    mapdcv.u
    mapdcv.s
    @25
    @26
    wph
    cY
    cS
    wcel
    @21
    mapdcv.y
    adantr
    mapdsord
    anbi12d
    rexbidva
    bitrd
    notbid
    anbi12d
    wph
    cE
    @7
    @0
    @1
    cD
    clmod
    vf
    @23
    mapdcv.e
    wph
    cD
    cH
    cK
    cW
    mapdcv.h
    mapdcv.d
    mapdcv.k
    lcdlmod
    wph
    cD
    cX
    cS
    @7
    cU
    cH
    cK
    cM
    cW
    mapdcv.h
    mapdcv.m
    mapdcv.u
    mapdcv.s
    mapdcv.d
    @23
    mapdcv.k
    mapdcv.x
    mapdcl2
    wph
    cD
    cY
    cS
    @7
    cU
    cH
    cK
    cM
    cW
    mapdcv.h
    mapdcv.m
    mapdcv.u
    mapdcv.s
    mapdcv.d
    @23
    mapdcv.k
    mapdcv.y
    mapdcl2
    lcvbr
    wph
    cC
    cS
    cX
    cY
    cU
    clmod
    vv
    mapdcv.s
    mapdcv.c
    wph
    cU
    cH
    cK
    cW
    mapdcv.h
    mapdcv.u
    mapdcv.k
    dvhlmod
    mapdcv.x
    mapdcv.y
    lcvbr
    3bitr4rd
end
