include "clmhm.mm"
include "co.mm"
include "wcel.mm"
include "clnm.mm"
include "w3a.mm"
include "clmod.mm"
include "cv.mm"
include "cress.mm"
include "clfig.mm"
include "clss.mm"
include "cfv.mm"
include "wral.mm"
include "lmhmlmod1.mm"
include "3ad2ant1.mm"
include "wa.mm"
include "cres.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "crn.mm"
include "eqid.mm"
include "reslmhm.mm"
include "3ad2antl1.mm"
include "cin.mm"
include "cnvresima.mm"
include "eqcomi.mm"
include "ineq1i.mm"
include "incom.mm"
include "3eqtri.mm"
include "oveq2i.mm"
include "oveq1i.mm"
include "cvv.mm"
include "wss.mm"
include "wceq.mm"
include "simpl1.mm"
include "cnvexg.mm"
include "imaexg.mm"
include "syl.mm"
include "syl5eqel.mm"
include "inss2.mm"
include "ressabs.mm"
include "sylancl.mm"
include "syl5eq.mm"
include "vex.mm"
include "inss1.mm"
include "mp2an.mm"
include "syl6reqr.mm"
include "simpl2.mm"
include "adantr.mm"
include "simpr.mm"
include "lmhmkerlss.mm"
include "lssincl.mm"
include "syl3anc.mm"
include "a1i.mm"
include "wb.mm"
include "lsslss.mm"
include "syl2anc.mm"
include "mpbir2and.mm"
include "lnmlssfg.mm"
include "eqeltrd.mm"
include "rnexg.mm"
include "resexg.mm"
include "ressress.mm"
include "resss.mm"
include "rnss.mm"
include "ax-mp.mm"
include "df-ss.mm"
include "mpbi.mm"
include "eqtr2i.mm"
include "simpl3.mm"
include "lmhmrnlss.mm"
include "lmhmlmod2.mm"
include "lmhmfgsplit.mm"
include "ralrimiva.mm"
include "islnm.mm"
include "sylanbrc.mm"

theorem lmhmlnmsplit
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cK: class K
  let cV: class V
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  assume lmhmfgsplit.z: |- .0. = ( 0g ` T )
  assume lmhmfgsplit.k: |- K = ( `' F " { .0. } )
  assume lmhmfgsplit.u: |- U = ( S |`s K )
  assume lmhmfgsplit.v: |- V = ( T |`s ran F )


  assert |- ( ( F e. ( S LMHom T ) /\ U e. LNoeM /\ V e. LNoeM ) -> S e. LNoeM )

  proof
    cF
    cS
    cT
    clmhm
    co
    #
    wcel
    #
    cU
    clnm
    wcel
    #
    cV
    clnm
    wcel
    #
    w3a
    #
    cS
    clmod
    wcel
    #
    cS
    va
    cv
    #
    cress
    co
    #
    clfig
    wcel
    #
    va
    cS
    clss
    cfv
    #
    wral
    cS
    clnm
    wcel
    @1
    @2
    @5
    @3
    cS
    cT
    cF
    lmhmlmod1
    3ad2ant1
    #
    @4
    @8
    va
    @9
    @4
    @6
    @9
    wcel
    #
    wa
    #
    cF
    @6
    cres
    #
    @7
    cT
    clmhm
    co
    wcel
    #
    @7
    @13
    ccnv
    c.0
    csn
    #
    cima
    #
    cress
    co
    #
    clfig
    wcel
    cT
    @13
    crn
    #
    cress
    co
    #
    clfig
    wcel
    @8
    @1
    @2
    @11
    @14
    @3
    @7
    cS
    cT
    @9
    cF
    @6
    @9
    eqid
    #
    @7
    eqid
    reslmhm
    3ad2antl1
    #
    @12
    @17
    cU
    @6
    cK
    cin
    #
    cress
    co
    #
    clfig
    @12
    @17
    @7
    @22
    cress
    co
    #
    @23
    @16
    @22
    @7
    cress
    @16
    cF
    ccnv
    #
    @15
    cima
    #
    @6
    cin
    cK
    @6
    cin
    @22
    @6
    @15
    cF
    cnvresima
    @26
    cK
    @6
    cK
    @26
    lmhmfgsplit.k
    eqcomi
    ineq1i
    cK
    @6
    incom
    3eqtri
    oveq2i
    @12
    @23
    cS
    @22
    cress
    co
    #
    @24
    @12
    @23
    cS
    cK
    cress
    co
    #
    @22
    cress
    co
    #
    @27
    cU
    @28
    @22
    cress
    lmhmfgsplit.u
    oveq1i
    @12
    cK
    cvv
    wcel
    #
    @22
    cK
    wss
    #
    @29
    @27
    wceq
    @12
    @1
    @30
    @1
    @2
    @3
    @11
    simpl1
    #
    @1
    cK
    @26
    cvv
    lmhmfgsplit.k
    @1
    @25
    cvv
    wcel
    @26
    cvv
    wcel
    cF
    @0
    cnvexg
    @25
    @15
    cvv
    imaexg
    syl
    syl5eqel
    syl
    @6
    cK
    inss2
    #
    cK
    @22
    cS
    cvv
    ressabs
    sylancl
    syl5eq
    @6
    cvv
    wcel
    @22
    @6
    wss
    @24
    @27
    wceq
    va
    vex
    @6
    cK
    inss1
    @6
    @22
    cS
    cvv
    ressabs
    mp2an
    syl6reqr
    syl5eq
    @12
    @2
    @22
    cU
    clss
    cfv
    #
    wcel
    #
    @23
    clfig
    wcel
    @1
    @2
    @3
    @11
    simpl2
    @12
    @35
    @22
    @9
    wcel
    #
    @31
    @12
    @5
    @11
    cK
    @9
    wcel
    #
    @36
    @4
    @5
    @11
    @10
    adantr
    #
    @4
    @11
    simpr
    @12
    @1
    @37
    @32
    cS
    cT
    @9
    cF
    cK
    c.0
    lmhmfgsplit.k
    lmhmfgsplit.z
    @20
    lmhmkerlss
    syl
    #
    @9
    @6
    cK
    cS
    @20
    lssincl
    syl3anc
    @31
    @12
    @33
    a1i
    @12
    @5
    @37
    @35
    @36
    @31
    wa
    wb
    @38
    @39
    @9
    @34
    cK
    @22
    cS
    cU
    lmhmfgsplit.u
    @20
    @34
    eqid
    #
    lsslss
    syl2anc
    mpbir2and
    @23
    @34
    @22
    cU
    @40
    @23
    eqid
    lnmlssfg
    syl2anc
    eqeltrd
    @12
    @19
    cV
    @18
    cress
    co
    #
    clfig
    @12
    @1
    @19
    @41
    wceq
    @32
    @1
    @41
    cT
    cF
    crn
    #
    @18
    cin
    #
    cress
    co
    #
    @19
    @1
    @41
    cT
    @42
    cress
    co
    #
    @18
    cress
    co
    #
    @44
    cV
    @45
    @18
    cress
    lmhmfgsplit.v
    oveq1i
    @1
    @42
    cvv
    wcel
    @18
    cvv
    wcel
    #
    @46
    @44
    wceq
    cF
    @0
    rnexg
    @1
    @13
    cvv
    wcel
    @47
    cF
    @6
    @0
    resexg
    @13
    cvv
    rnexg
    syl
    @42
    @18
    cT
    cvv
    cvv
    ressress
    syl2anc
    syl5eq
    @18
    @43
    cT
    cress
    @43
    @18
    @42
    cin
    #
    @18
    @42
    @18
    incom
    @18
    @42
    wss
    #
    @48
    @18
    wceq
    @13
    cF
    wss
    @49
    cF
    @6
    resss
    @13
    cF
    rnss
    ax-mp
    #
    @18
    @42
    df-ss
    mpbi
    eqtr2i
    oveq2i
    syl6reqr
    syl
    @12
    @3
    @18
    cV
    clss
    cfv
    #
    wcel
    #
    @41
    clfig
    wcel
    @1
    @2
    @3
    @11
    simpl3
    @12
    @52
    @18
    cT
    clss
    cfv
    #
    wcel
    #
    @49
    @12
    @14
    @54
    @21
    @7
    cT
    @13
    lmhmrnlss
    syl
    @49
    @12
    @50
    a1i
    @12
    cT
    clmod
    wcel
    #
    @42
    @53
    wcel
    #
    @52
    @54
    @49
    wa
    wb
    @12
    @1
    @55
    @32
    cS
    cT
    cF
    lmhmlmod2
    syl
    @12
    @1
    @56
    @32
    cS
    cT
    cF
    lmhmrnlss
    syl
    @53
    @51
    @42
    @18
    cT
    cV
    lmhmfgsplit.v
    @53
    eqid
    @51
    eqid
    #
    lsslss
    syl2anc
    mpbir2and
    @41
    @51
    @18
    cV
    @57
    @41
    eqid
    lnmlssfg
    syl2anc
    eqeltrd
    @7
    cT
    @17
    @13
    @16
    @19
    c.0
    lmhmfgsplit.z
    @16
    eqid
    @17
    eqid
    @19
    eqid
    lmhmfgsplit
    syl3anc
    ralrimiva
    @9
    va
    cS
    @20
    islnm
    sylanbrc
end
