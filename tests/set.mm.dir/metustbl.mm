include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "cmetu.mm"
include "w3a.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "wss.mm"
include "wa.mm"
include "cbl.mm"
include "crn.mm"
include "wrex.mm"
include "co.mm"
include "crp.mm"
include "ccnv.mm"
include "cc0.mm"
include "cico.mm"
include "simp1.mm"
include "simp3.mm"
include "cmpt.mm"
include "wceq.mm"
include "simpr.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "eqid.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "biimpi.mm"
include "ad2antlr.mm"
include "sseq1.mm"
include "biimpcd.mm"
include "reximdv.mm"
include "sylc.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "syl.mm"
include "simp2.mm"
include "cxp.mm"
include "metuel.mm"
include "simplbda.mm"
include "syl21anc.mm"
include "r19.29a.mm"
include "imass1.mm"
include "reximi.mm"
include "blval2.mm"
include "sseq1d.mm"
include "3expa.mm"
include "rexbidva.mm"
include "syl5ibr.mm"
include "imp.mm"
include "blssexps.mm"
include "3adant2.mm"
include "mpbird.mm"

theorem metustbl
  let cD: class D
  let cP: class P
  let cV: class V
  let cX: class X
  let va: setvar a
  let vr: setvar r
  let vw: setvar w

  disjoint D a
  disjoint P a
  disjoint V a
  disjoint X a
  disjoint a r
  disjoint a w
  disjoint r w
  disjoint D r
  disjoint D w
  disjoint P r
  disjoint P w
  disjoint V r
  disjoint V w
  disjoint X r
  disjoint X w
  assert |- ( ( D e. ( PsMet ` X ) /\ V e. ( metUnif ` D ) /\ P e. X ) -> E. a e. ran ( ball ` D ) ( P e. a /\ a C_ ( V " { P } ) ) )

  proof
    cD
    cX
    cpsmet
    cfv
    wcel
    #
    cV
    cD
    cmetu
    cfv
    wcel
    #
    cP
    cX
    wcel
    #
    w3a
    #
    cP
    va
    cv
    #
    wcel
    @4
    cV
    cP
    csn
    #
    cima
    #
    wss
    wa
    va
    cD
    cbl
    cfv
    #
    crn
    wrex
    #
    cP
    vr
    cv
    #
    @7
    co
    #
    @6
    wss
    #
    vr
    crp
    wrex
    #
    @3
    @0
    @2
    cD
    ccnv
    cc0
    @9
    cico
    co
    cima
    #
    cV
    wss
    #
    vr
    crp
    wrex
    #
    @12
    @0
    @1
    @2
    simp1
    #
    @0
    @1
    @2
    simp3
    #
    @3
    vw
    cv
    #
    cV
    wss
    #
    @15
    vw
    vr
    crp
    @13
    cmpt
    #
    crn
    #
    @3
    @18
    @21
    wcel
    #
    wa
    #
    @19
    wa
    @19
    @18
    @13
    wceq
    #
    vr
    crp
    wrex
    #
    @15
    @23
    @19
    simpr
    @22
    @25
    @3
    @19
    @22
    @25
    @18
    cvv
    wcel
    @22
    @25
    wb
    vw
    vex
    vr
    crp
    @13
    @18
    @20
    cvv
    @20
    eqid
    elrnmpt
    ax-mp
    biimpi
    ad2antlr
    @19
    @24
    @14
    vr
    crp
    @24
    @19
    @14
    @18
    @13
    cV
    sseq1
    biimpcd
    reximdv
    sylc
    @3
    cX
    c0
    wne
    #
    @0
    @1
    @19
    vw
    @21
    wrex
    #
    @3
    @2
    @26
    @17
    cX
    cP
    ne0i
    syl
    @16
    @0
    @1
    @2
    simp2
    @26
    @0
    wa
    @1
    cV
    cX
    cX
    cxp
    wss
    @27
    vw
    cD
    cV
    cX
    vr
    metuel
    simplbda
    syl21anc
    r19.29a
    @0
    @2
    wa
    #
    @15
    @12
    @15
    @12
    @28
    @13
    @5
    cima
    #
    @6
    wss
    #
    vr
    crp
    wrex
    @14
    @30
    vr
    crp
    @13
    cV
    @5
    imass1
    reximi
    @28
    @11
    @30
    vr
    crp
    @0
    @2
    @9
    crp
    wcel
    #
    @11
    @30
    wb
    @0
    @2
    @31
    w3a
    @10
    @29
    @6
    cD
    cP
    @9
    cX
    blval2
    sseq1d
    3expa
    rexbidva
    syl5ibr
    imp
    syl21anc
    @0
    @2
    @8
    @12
    wb
    @1
    va
    @6
    cD
    cP
    cX
    vr
    blssexps
    3adant2
    mpbird
end
