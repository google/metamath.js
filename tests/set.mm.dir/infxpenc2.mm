include "con0.mm"
include "wcel.mm"
include "com.mm"
include "cv.mm"
include "wss.mm"
include "coe.mm"
include "co.mm"
include "cfv.mm"
include "wf1o.mm"
include "c1o.mm"
include "cdif.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "wex.mm"
include "c2o.mm"
include "cxp.mm"
include "cnfcom3c.mm"
include "cen.mm"
include "wbr.mm"
include "comu.mm"
include "csuc.mm"
include "df-2o.mm"
include "oveq2i.mm"
include "wceq.mm"
include "omelon.mm"
include "1on.mm"
include "oesuc.mm"
include "mp2an.mm"
include "oe1.mm"
include "ax-mp.mm"
include "oveq1i.mm"
include "3eqtri.mm"
include "omxpen.mm"
include "eqbrtri.mm"
include "xpomen.mm"
include "entri.mm"
include "a1i.mm"
include "bren.mm"
include "sylib.mm"
include "wa.mm"
include "eeanv.mm"
include "cid.mm"
include "c0.mm"
include "ccnv.mm"
include "cpr.mm"
include "cres.mm"
include "cop.mm"
include "cun.mm"
include "ccom.mm"
include "crn.mm"
include "cmpt.mm"
include "simpl.mm"
include "simprl.mm"
include "sseq2.mm"
include "wb.mm"
include "oveq2.mm"
include "f1oeq3.mm"
include "syl.mm"
include "cbvrexv.mm"
include "fveq2.mm"
include "f1oeq1.mm"
include "f1oeq2.mm"
include "bitrd.mm"
include "rexbidv.mm"
include "syl5bb.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "cbvmptv.mm"
include "cnveqi.mm"
include "fveq1i.mm"
include "2on.mm"
include "peano1.mm"
include "oen0.mm"
include "mpan2.mm"
include "eqid.mm"
include "fveqf1o.mm"
include "mp3an23.mm"
include "ad2antll.mm"
include "simpld.mm"
include "simprd.mm"
include "infxpenc2lem3.mm"
include "ex.mm"
include "exlimdvv.mm"
include "syl5bir.mm"
include "mp2and.mm"

theorem infxpenc2
  let cA: class A
  let vg: setvar g
  let vb: setvar b
  let vf: setvar f
  let vn: setvar n
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint b g
  disjoint A b
  disjoint A g
  disjoint b f
  disjoint b n
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint f g
  disjoint f n
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g n
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  assert |- ( A e. On -> E. g A. b e. A ( _om C_ b -> ( g ` b ) : ( b X. b ) -1-1-onto-> b ) )

  proof
    cA
    con0
    wcel
    #
    com
    vx
    cv
    #
    wss
    #
    @1
    com
    vy
    cv
    #
    coe
    co
    #
    @1
    vn
    cv
    #
    cfv
    #
    wf1o
    #
    vy
    con0
    c1o
    cdif
    #
    wrex
    #
    wi
    #
    vx
    cA
    wral
    #
    vn
    wex
    #
    com
    c2o
    coe
    co
    #
    com
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    com
    vb
    cv
    #
    wss
    #
    @17
    @17
    cxp
    @17
    @17
    vg
    cv
    cfv
    wf1o
    wi
    vb
    cA
    wral
    vg
    wex
    #
    vy
    cA
    vn
    vx
    cnfcom3c
    @0
    @13
    com
    cen
    wbr
    #
    @16
    @20
    @0
    @13
    com
    com
    cxp
    #
    com
    @13
    com
    com
    comu
    co
    #
    @21
    cen
    @13
    com
    c1o
    csuc
    #
    coe
    co
    #
    com
    c1o
    coe
    co
    #
    com
    comu
    co
    #
    @22
    c2o
    @23
    com
    coe
    df-2o
    oveq2i
    com
    con0
    wcel
    #
    c1o
    con0
    wcel
    @24
    @26
    wceq
    omelon
    1on
    com
    c1o
    oesuc
    mp2an
    @25
    com
    com
    comu
    @27
    @25
    com
    wceq
    omelon
    com
    oe1
    ax-mp
    oveq1i
    3eqtri
    @27
    @27
    @22
    @21
    cen
    wbr
    omelon
    omelon
    com
    com
    omxpen
    mp2an
    eqbrtri
    xpomen
    entri
    a1i
    @13
    com
    vf
    bren
    sylib
    @12
    @16
    wa
    @11
    @15
    wa
    #
    vf
    wex
    vn
    wex
    @0
    @19
    @11
    @15
    vn
    vf
    eeanv
    @0
    @28
    @19
    vn
    vf
    @0
    @28
    @19
    @0
    @28
    wa
    #
    vz
    vw
    cA
    vg
    vn
    @14
    cid
    @13
    c0
    c0
    @14
    ccnv
    cfv
    #
    cpr
    cdif
    cres
    c0
    @30
    cop
    @30
    c0
    cop
    cpr
    cun
    ccom
    #
    @17
    @5
    cfv
    #
    crn
    #
    vb
    @8
    com
    @17
    coe
    co
    #
    cmpt
    #
    ccnv
    #
    cfv
    vb
    @0
    @28
    simpl
    @29
    @11
    @18
    @17
    com
    vw
    cv
    #
    coe
    co
    #
    @32
    wf1o
    #
    vw
    @8
    wrex
    #
    wi
    #
    vb
    cA
    wral
    @0
    @11
    @15
    simprl
    @10
    @41
    vx
    vb
    cA
    @1
    @17
    wceq
    #
    @2
    @18
    @9
    @40
    @1
    @17
    com
    sseq2
    @9
    @1
    @38
    @6
    wf1o
    #
    vw
    @8
    wrex
    @42
    @40
    @7
    @43
    vy
    vw
    @8
    @3
    @37
    wceq
    @4
    @38
    wceq
    @7
    @43
    wb
    @3
    @37
    com
    coe
    oveq2
    @4
    @38
    @1
    @6
    f1oeq3
    syl
    cbvrexv
    @42
    @43
    @39
    vw
    @8
    @42
    @43
    @1
    @38
    @32
    wf1o
    #
    @39
    @42
    @6
    @32
    wceq
    @43
    @44
    wb
    @1
    @17
    @5
    fveq2
    @1
    @38
    @6
    @32
    f1oeq1
    syl
    @1
    @17
    @38
    @32
    f1oeq2
    bitrd
    rexbidv
    syl5bb
    imbi12d
    cbvralv
    sylib
    @33
    @36
    vz
    @8
    com
    vz
    cv
    #
    coe
    co
    #
    cmpt
    #
    ccnv
    @35
    @47
    vb
    vz
    @8
    @34
    @46
    @17
    @45
    com
    coe
    oveq2
    cbvmptv
    cnveqi
    fveq1i
    @29
    @13
    com
    @31
    wf1o
    #
    c0
    @31
    cfv
    c0
    wceq
    #
    @15
    @48
    @49
    wa
    #
    @0
    @11
    @15
    c0
    @13
    wcel
    #
    c0
    com
    wcel
    #
    @50
    @27
    c2o
    con0
    wcel
    #
    @51
    omelon
    2on
    @27
    @53
    wa
    @52
    @51
    peano1
    com
    c2o
    oen0
    mpan2
    mp2an
    peano1
    @13
    com
    c0
    c0
    @14
    @31
    @31
    eqid
    fveqf1o
    mp3an23
    ad2antll
    #
    simpld
    @29
    @48
    @49
    @54
    simprd
    infxpenc2lem3
    ex
    exlimdvv
    syl5bir
    mp2and
end
