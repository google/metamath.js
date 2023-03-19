include "cv.mm"
include "wcel.mm"
include "crnk.mm"
include "cfv.mm"
include "com.mm"
include "cima.mm"
include "ciun.mm"
include "cep.mm"
include "coi.mm"
include "cdm.mm"
include "crn.mm"
include "cuni.mm"
include "cxp.mm"
include "cpw.mm"
include "char.mm"
include "cid.mm"
include "cres.mm"
include "ctc.mm"
include "cr1.mm"
include "con0.mm"
include "wceq.mm"
include "cdom.mm"
include "wbr.mm"
include "csn.mm"
include "wral.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sseli.mm"
include "tcrank.mm"
include "syl.mm"
include "wfn.mm"
include "itunifn.mm"
include "fniunfv.mm"
include "itunitc.mm"
include "syl6reqr.mm"
include "imaeq2d.mm"
include "imaiun.mm"
include "a1i.mm"
include "3eqtrd.mm"
include "dmresi.mm"
include "syl6eqr.mm"
include "word.mm"
include "rankon.mm"
include "syl6eqelr.mm"
include "eloni.mm"
include "oiid.mm"
include "3syl.mm"
include "dmeqd.mm"
include "eqtr4d.mm"
include "cwdom.mm"
include "wa.mm"
include "cvv.mm"
include "omex.mm"
include "wdomref.mm"
include "mp1i.mm"
include "cmpt.mm"
include "crdg.mm"
include "frfnom.mm"
include "fneq1i.mm"
include "mpbir.mm"
include "ax-mp.mm"
include "iunon.mm"
include "mpan.mm"
include "hsmexlem9.mm"
include "mprg.mm"
include "eqeltrri.mm"
include "fvssunirn.mm"
include "eqid.mm"
include "hsmexlem4.mm"
include "ancoms.mm"
include "sseldi.mm"
include "wss.mm"
include "imassrn.mm"
include "wf.mm"
include "rankf.mm"
include "frn.mm"
include "sstri.mm"
include "wfun.mm"
include "ffun.mm"
include "fvex.mm"
include "funimaex.mm"
include "mp2b.mm"
include "elpw.mm"
include "jctil.mm"
include "ralrimiva.mm"
include "hsmexlem3.mm"
include "syl21anc.mm"
include "eqeltrd.mm"

theorem hsmexlem5
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cS: class S
  let cU: class U
  let cH: class H
  let cO: class O
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  assume hsmexlem4.x: |- X e. _V
  assume hsmexlem4.h: |- H = ( rec ( ( z e. _V |-> ( har ` ~P ( X X. z ) ) ) , ( har ` ~P X ) ) |` _om )
  assume hsmexlem4.u: |- U = ( x e. _V |-> ( rec ( ( y e. _V |-> U. y ) , x ) |` _om ) )
  assume hsmexlem4.s: |- S = { a e. U. ( R1 " On ) | A. b e. ( TC ` { a } ) b ~<_ X }
  assume hsmexlem4.o: |- O = OrdIso ( _E , ( rank " ( ( U ` d ) ` c ) ) )

  disjoint a c
  disjoint a d
  disjoint H a
  disjoint c d
  disjoint H c
  disjoint H d
  disjoint S c
  disjoint S d
  disjoint U c
  disjoint U d
  disjoint a b
  disjoint a z
  disjoint X a
  disjoint b z
  disjoint X b
  disjoint X z
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b d
  disjoint b x
  disjoint b y
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint a e
  disjoint a f
  disjoint c e
  disjoint c f
  disjoint d e
  disjoint d f
  disjoint e f
  disjoint H e
  disjoint H f
  disjoint O e
  disjoint S e
  disjoint S f
  disjoint U f
  disjoint b e
  disjoint b f
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint f x
  disjoint f y
  disjoint f z
  assert |- ( d e. S -> ( rank ` d ) e. ( har ` ~P ( _om X. U. ran H ) ) )

  proof
    vd
    cv
    #
    cS
    wcel
    #
    @0
    crnk
    cfv
    #
    vc
    com
    crnk
    vc
    cv
    #
    @0
    cU
    cfv
    #
    cfv
    #
    cima
    #
    ciun
    #
    cep
    coi
    #
    cdm
    #
    com
    cH
    crn
    cuni
    #
    cxp
    cpw
    char
    cfv
    #
    @1
    @2
    cid
    @7
    cres
    #
    cdm
    #
    @9
    @1
    @2
    @7
    @13
    @1
    @2
    crnk
    @0
    ctc
    cfv
    #
    cima
    #
    crnk
    vc
    com
    @5
    ciun
    #
    cima
    #
    @7
    @1
    @0
    cr1
    con0
    cima
    cuni
    #
    wcel
    @2
    @15
    wceq
    cS
    @18
    @0
    cS
    vb
    cv
    cX
    cdom
    wbr
    vb
    va
    cv
    #
    csn
    ctc
    cfv
    wral
    #
    va
    @18
    crab
    @18
    hsmexlem4.s
    @20
    va
    @18
    ssrab2
    eqsstri
    sseli
    @0
    tcrank
    syl
    @1
    @14
    @16
    crnk
    @1
    @16
    @4
    crn
    cuni
    #
    @14
    @1
    @4
    com
    wfn
    @16
    @21
    wceq
    vx
    vy
    @0
    cU
    cS
    hsmexlem4.u
    itunifn
    vc
    com
    @4
    fniunfv
    syl
    vx
    vy
    @0
    cU
    hsmexlem4.u
    itunitc
    syl6reqr
    imaeq2d
    @17
    @7
    wceq
    @1
    vc
    crnk
    com
    @5
    imaiun
    a1i
    3eqtrd
    #
    @7
    dmresi
    syl6eqr
    @1
    @8
    @12
    @1
    @7
    con0
    wcel
    @7
    word
    @8
    @12
    wceq
    @1
    @7
    @2
    con0
    @22
    @0
    rankon
    syl6eqelr
    @7
    eloni
    @7
    oiid
    3syl
    dmeqd
    eqtr4d
    @1
    com
    com
    cwdom
    wbr
    #
    @10
    con0
    wcel
    #
    @6
    con0
    cpw
    wcel
    #
    @6
    cep
    coi
    #
    cdm
    #
    @10
    wcel
    #
    wa
    #
    vc
    com
    wral
    @9
    @11
    wcel
    com
    cvv
    wcel
    #
    @23
    @1
    omex
    cvv
    com
    wdomref
    mp1i
    @24
    @1
    va
    com
    @19
    cH
    cfv
    #
    ciun
    #
    @10
    con0
    cH
    com
    wfn
    #
    @32
    @10
    wceq
    @33
    vz
    cvv
    cX
    vz
    cv
    cxp
    cpw
    char
    cfv
    cmpt
    #
    cX
    cpw
    char
    cfv
    #
    crdg
    com
    cres
    #
    com
    wfn
    @35
    @34
    frfnom
    com
    cH
    @36
    hsmexlem4.h
    fneq1i
    mpbir
    va
    com
    cH
    fniunfv
    ax-mp
    @31
    con0
    wcel
    #
    @32
    con0
    wcel
    #
    va
    com
    @30
    @37
    va
    com
    wral
    @38
    omex
    va
    com
    @31
    cvv
    iunon
    mpan
    vz
    cH
    cX
    va
    hsmexlem4.h
    hsmexlem9
    mprg
    eqeltrri
    a1i
    @1
    @29
    vc
    com
    @1
    @3
    com
    wcel
    #
    wa
    #
    @28
    @25
    @40
    @3
    cH
    cfv
    #
    @10
    @27
    cH
    @3
    fvssunirn
    @39
    @1
    @27
    @41
    wcel
    vx
    vy
    vz
    cS
    cU
    cH
    @26
    cX
    va
    vb
    vc
    vd
    hsmexlem4.x
    hsmexlem4.h
    hsmexlem4.u
    hsmexlem4.s
    @26
    eqid
    #
    hsmexlem4
    ancoms
    sseldi
    @25
    @6
    con0
    wss
    @6
    crnk
    crn
    #
    con0
    crnk
    @5
    imassrn
    @18
    con0
    crnk
    wf
    #
    @43
    con0
    wss
    rankf
    @18
    con0
    crnk
    frn
    ax-mp
    sstri
    @6
    con0
    @44
    crnk
    wfun
    @6
    cvv
    wcel
    rankf
    @18
    con0
    crnk
    ffun
    crnk
    @5
    @3
    @4
    fvex
    funimaex
    mp2b
    elpw
    mpbir
    jctil
    ralrimiva
    com
    @6
    @10
    com
    @26
    @8
    vc
    @42
    @8
    eqid
    hsmexlem3
    syl21anc
    eqeltrd
end
