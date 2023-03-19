include "wcel.mm"
include "cpw.mm"
include "ctop.mm"
include "wceq.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "crab.mm"
include "cfn.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "clocfin.mm"
include "cfv.mm"
include "distop.mm"
include "eqidd.mm"
include "csn.mm"
include "snelpwi.mm"
include "adantl.mm"
include "vsnid.mm"
include "a1i.mm"
include "nfv.mm"
include "nfrab1.mm"
include "nfcv.mm"
include "abeq2i.mm"
include "anbi1i.mm"
include "simpr.mm"
include "wn.mm"
include "simplr.mm"
include "ineq1d.mm"
include "disjsn2.mm"
include "eqtrd.mm"
include "simp-4r.mm"
include "neneqd.mm"
include "pm2.65da.mm"
include "nne.mm"
include "sylib.mm"
include "sneqd.mm"
include "r19.29an.mm"
include "an32s.mm"
include "anasss.mm"
include "sneq.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "adantll.mm"
include "inidm.mm"
include "syl6eq.mm"
include "vex.mm"
include "snnz.mm"
include "eqnetrd.mm"
include "jca.mm"
include "impbida.mm"
include "syl5bb.mm"
include "rabid.mm"
include "velsn.mm"
include "3bitr4g.mm"
include "eqrd.mm"
include "snfi.mm"
include "syl6eqel.mm"
include "eleq2.mm"
include "ineq2.mm"
include "neeq1d.mm"
include "rabbidv.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "syl12anc.mm"
include "ralrimiva.mm"
include "cuni.mm"
include "unipw.mm"
include "eqcomi.mm"
include "unisngl.mm"
include "islocfin.mm"
include "syl3anbrc.mm"

theorem dissnlocfin
  let vx: setvar x
  let vu: setvar u
  let cC: class C
  let cV: class V
  let cX: class X
  let vy: setvar y
  let vz: setvar z
  let cY: class Y
  assume dissnref.c: |- C = { u | E. x e. X u = { x } }

  disjoint C u
  disjoint C x
  disjoint u x
  disjoint V u
  disjoint V x
  disjoint X u
  disjoint X x
  disjoint C y
  disjoint C z
  disjoint u y
  disjoint u z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint V y
  disjoint V z
  disjoint X y
  disjoint X z
  disjoint Y u
  disjoint Y x
  disjoint Y y
  assert |- ( X e. V -> C e. ( LocFin ` ~P X ) )

  proof
    cX
    cV
    wcel
    #
    cX
    cpw
    #
    ctop
    wcel
    cX
    cX
    wceq
    vz
    cv
    #
    vy
    cv
    #
    wcel
    #
    vu
    cv
    #
    @3
    cin
    #
    c0
    wne
    #
    vu
    cC
    crab
    #
    cfn
    wcel
    #
    wa
    #
    vy
    @1
    wrex
    #
    vz
    cX
    wral
    cC
    @1
    clocfin
    cfv
    wcel
    cX
    cV
    distop
    @0
    cX
    eqidd
    @0
    @11
    vz
    cX
    @0
    @2
    cX
    wcel
    #
    wa
    #
    @2
    csn
    #
    @1
    wcel
    #
    @2
    @14
    wcel
    #
    @5
    @14
    cin
    #
    c0
    wne
    #
    vu
    cC
    crab
    #
    cfn
    wcel
    #
    @11
    @12
    @15
    @0
    @2
    cX
    snelpwi
    adantl
    @16
    @13
    vz
    vsnid
    a1i
    @13
    @19
    @14
    csn
    #
    cfn
    @13
    vu
    @19
    @21
    @13
    vu
    nfv
    @18
    vu
    cC
    nfrab1
    vu
    @21
    nfcv
    @13
    @5
    cC
    wcel
    #
    @18
    wa
    #
    @5
    @14
    wceq
    #
    @5
    @19
    wcel
    @5
    @21
    wcel
    @23
    @5
    vx
    cv
    #
    csn
    #
    wceq
    #
    vx
    cX
    wrex
    #
    @18
    wa
    #
    @13
    @24
    @22
    @28
    @18
    @28
    vu
    cC
    dissnref.c
    abeq2i
    anbi1i
    @13
    @29
    @24
    @13
    @28
    @18
    @24
    @13
    @18
    @28
    @24
    @13
    @18
    wa
    #
    @27
    @24
    vx
    cX
    @30
    @25
    cX
    wcel
    #
    wa
    #
    @27
    wa
    #
    @5
    @26
    @14
    @32
    @27
    simpr
    @33
    @25
    @2
    @33
    @25
    @2
    wne
    #
    wn
    @25
    @2
    wceq
    #
    @33
    @34
    @17
    c0
    wceq
    @33
    @34
    wa
    #
    @17
    @26
    @14
    cin
    #
    c0
    @36
    @5
    @26
    @14
    @32
    @27
    @34
    simplr
    ineq1d
    @34
    @37
    c0
    wceq
    @33
    @25
    @2
    disjsn2
    adantl
    eqtrd
    @36
    @17
    c0
    @13
    @18
    @31
    @27
    @34
    simp-4r
    neneqd
    pm2.65da
    @25
    @2
    nne
    sylib
    sneqd
    eqtrd
    r19.29an
    an32s
    anasss
    @13
    @24
    wa
    #
    @28
    @18
    @12
    @24
    @28
    @0
    @27
    @24
    vx
    @2
    cX
    @35
    @26
    @14
    @5
    @25
    @2
    sneq
    eqeq2d
    rspcev
    adantll
    @38
    @17
    @14
    c0
    @38
    @17
    @14
    @14
    cin
    @14
    @38
    @5
    @14
    @14
    @13
    @24
    simpr
    ineq1d
    @14
    inidm
    syl6eq
    @14
    c0
    wne
    @38
    @2
    vz
    vex
    snnz
    a1i
    eqnetrd
    jca
    impbida
    syl5bb
    @18
    vu
    cC
    rabid
    vu
    @14
    velsn
    3bitr4g
    eqrd
    @14
    snfi
    syl6eqel
    @10
    @16
    @20
    wa
    vy
    @14
    @1
    @3
    @14
    wceq
    #
    @4
    @16
    @9
    @20
    @3
    @14
    @2
    eleq2
    @39
    @8
    @19
    cfn
    @39
    @7
    @18
    vu
    cC
    @39
    @6
    @17
    c0
    @3
    @14
    @5
    ineq2
    neeq1d
    rabbidv
    eleq1d
    anbi12d
    rspcev
    syl12anc
    ralrimiva
    vz
    cC
    vy
    @1
    cX
    cX
    vu
    @1
    cuni
    cX
    cX
    unipw
    eqcomi
    vx
    vu
    cC
    cX
    dissnref.c
    unisngl
    islocfin
    syl3anbrc
end
