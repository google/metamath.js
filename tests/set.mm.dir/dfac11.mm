include "wac.mm"
include "cv.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "wex.mm"
include "wal.mm"
include "dfac3.mm"
include "wceq.mm"
include "raleq.mm"
include "exbidv.mm"
include "cbvalv.mm"
include "cmpt.mm"
include "neeq1.mm"
include "fveq2.mm"
include "id.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "w3a.mm"
include "sneqd.mm"
include "eqid.mm"
include "snex.mm"
include "fvmpt.mm"
include "3ad2ant1.mm"
include "wss.mm"
include "simp3.mm"
include "snssd.mm"
include "elpw.mm"
include "sylibr.mm"
include "snfi.mm"
include "a1i.mm"
include "elind.mm"
include "fvex.mm"
include "snnz.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "eqeltrd.mm"
include "3exp.mm"
include "a2d.mm"
include "ralimia.mm"
include "sylbi.mm"
include "vex.mm"
include "mptex.mm"
include "fveq1.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "spcev.mm"
include "syl.mm"
include "exlimiv.mm"
include "alimi.mm"
include "wwe.mm"
include "crnk.mm"
include "cr1.mm"
include "pwex.mm"
include "spcv.mm"
include "con0.mm"
include "rankon.mm"
include "aomclem8.mm"
include "cvv.mm"
include "r1rankid.mm"
include "wess.mm"
include "eximdv.mm"
include "mp2b.mm"
include "3syl.mm"
include "alrimiv.mm"
include "dfac8.mm"
include "impbii.mm"

theorem dfac11
  let vx: setvar x
  let vz: setvar z
  let vf: setvar f
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d

  disjoint x z
  disjoint f x
  disjoint f z
  disjoint a x
  disjoint b x
  disjoint c x
  disjoint d x
  disjoint a z
  disjoint b z
  disjoint c z
  disjoint d z
  disjoint a f
  disjoint b f
  disjoint c f
  disjoint d f
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint b c
  disjoint b d
  disjoint c d
  assert |- ( CHOICE <-> A. x E. f A. z e. x ( z =/= (/) -> ( f ` z ) e. ( ( ~P z i^i Fin ) \ { (/) } ) ) )

  proof
    wac
    vz
    cv
    #
    c0
    wne
    #
    @0
    vf
    cv
    #
    cfv
    #
    @0
    cpw
    #
    cfn
    cin
    #
    c0
    csn
    cdif
    #
    wcel
    #
    wi
    #
    vz
    vx
    cv
    #
    wral
    #
    vf
    wex
    #
    vx
    wal
    #
    wac
    vd
    cv
    #
    c0
    wne
    #
    @13
    vc
    cv
    #
    cfv
    #
    @13
    wcel
    #
    wi
    #
    vd
    va
    cv
    #
    wral
    #
    vc
    wex
    #
    va
    wal
    #
    @12
    va
    vd
    vc
    dfac3
    @22
    @18
    vd
    @9
    wral
    #
    vc
    wex
    #
    vx
    wal
    @12
    @21
    @24
    va
    vx
    @19
    @9
    wceq
    @20
    @23
    vc
    @18
    vd
    @19
    @9
    raleq
    exbidv
    cbvalv
    @24
    @11
    vx
    @23
    @11
    vc
    @23
    @1
    @0
    vb
    @9
    vb
    cv
    #
    @15
    cfv
    #
    csn
    #
    cmpt
    #
    cfv
    #
    @6
    wcel
    #
    wi
    #
    vz
    @9
    wral
    #
    @11
    @23
    @1
    @0
    @15
    cfv
    #
    @0
    wcel
    #
    wi
    #
    vz
    @9
    wral
    @32
    @18
    @35
    vd
    vz
    @9
    @13
    @0
    wceq
    #
    @14
    @1
    @17
    @34
    @13
    @0
    c0
    neeq1
    @36
    @16
    @33
    @13
    @0
    @13
    @0
    @15
    fveq2
    @36
    id
    eleq12d
    imbi12d
    cbvralv
    @35
    @31
    vz
    @9
    @0
    @9
    wcel
    #
    @1
    @34
    @30
    @37
    @1
    @34
    @30
    @37
    @1
    @34
    w3a
    #
    @29
    @33
    csn
    #
    @6
    @37
    @1
    @29
    @39
    wceq
    @34
    vb
    @0
    @27
    @39
    @9
    @28
    @25
    @0
    wceq
    @26
    @33
    @25
    @0
    @15
    fveq2
    sneqd
    @28
    eqid
    @33
    snex
    #
    fvmpt
    3ad2ant1
    @38
    @39
    @5
    wcel
    @39
    c0
    wne
    #
    @39
    @6
    wcel
    @38
    @4
    cfn
    @39
    @38
    @39
    @0
    wss
    @39
    @4
    wcel
    @38
    @33
    @0
    @37
    @1
    @34
    simp3
    snssd
    @39
    @0
    @40
    elpw
    sylibr
    @39
    cfn
    wcel
    @38
    @33
    snfi
    a1i
    elind
    @41
    @38
    @33
    @0
    @15
    fvex
    snnz
    a1i
    @39
    @5
    c0
    eldifsn
    sylanbrc
    eqeltrd
    3exp
    a2d
    ralimia
    sylbi
    @10
    @32
    vf
    @28
    vb
    @9
    @27
    vx
    vex
    mptex
    @2
    @28
    wceq
    #
    @8
    @31
    vz
    @9
    @42
    @7
    @30
    @1
    @42
    @3
    @29
    @6
    @0
    @2
    @28
    fveq1
    eleq1d
    imbi2d
    ralbidv
    spcev
    syl
    exlimiv
    alimi
    sylbi
    sylbi
    @12
    @19
    @25
    wwe
    #
    vb
    wex
    #
    va
    wal
    wac
    @12
    @44
    va
    @12
    @8
    vz
    @19
    crnk
    cfv
    #
    cr1
    cfv
    #
    cpw
    #
    wral
    #
    vf
    wex
    #
    @46
    @25
    wwe
    #
    vb
    wex
    #
    @44
    @11
    @49
    vx
    @47
    @46
    @45
    cr1
    fvex
    pwex
    @9
    @47
    wceq
    @10
    @48
    vf
    @8
    vz
    @9
    @47
    raleq
    exbidv
    spcv
    @48
    @51
    vf
    @48
    vf
    @45
    vz
    vb
    @45
    con0
    wcel
    @48
    @19
    rankon
    a1i
    @48
    id
    aomclem8
    exlimiv
    @19
    cvv
    wcel
    @19
    @46
    wss
    #
    @51
    @44
    wi
    va
    vex
    @19
    cvv
    r1rankid
    @52
    @50
    @43
    vb
    @19
    @46
    @25
    wess
    eximdv
    mp2b
    3syl
    alrimiv
    va
    vb
    dfac8
    sylibr
    impbii
end
