include "csx.mm"
include "co.mm"
include "cmbfm.mm"
include "wcel.mm"
include "cuni.mm"
include "wf.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "cxp.mm"
include "cmpt2.mm"
include "crn.mm"
include "wral.mm"
include "cfv.mm"
include "cop.mm"
include "wa.mm"
include "mbfmf.mm"
include "ffvelrnda.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "wceq.mm"
include "csiga.mm"
include "sxuni.mm"
include "adantr.mm"
include "eleqtrd.mm"
include "fmptd.mm"
include "wrex.mm"
include "eqid.mm"
include "vex.mm"
include "xpex.mm"
include "elrnmpt2.mm"
include "w3a.mm"
include "simp3.mm"
include "imaeq2d.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp2r.mm"
include "cin.mm"
include "xppreima2.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "mbfmcnvima.mm"
include "inelsiga.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "3expia.mm"
include "rexlimdvva.mm"
include "imp.mm"
include "sylan2b.mm"
include "ralrimiva.mm"
include "cvv.mm"
include "txbasex.mm"
include "csigagen.mm"
include "sxval.mm"
include "imambfm.mm"
include "mpbir2and.mm"

theorem mbfmco2
  let wph: wff ph
  let vx: setvar x
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume mbfmco.1: |- ( ph -> R e. U. ran sigAlgebra )
  assume mbfmco.2: |- ( ph -> S e. U. ran sigAlgebra )
  assume mbfmco.3: |- ( ph -> T e. U. ran sigAlgebra )
  assume mbfmco2.4: |- ( ph -> F e. ( R MblFnM S ) )
  assume mbfmco2.5: |- ( ph -> G e. ( R MblFnM T ) )
  assume mbfmco2.6: |- H = ( x e. U. R |-> <. ( F ` x ) , ( G ` x ) >. )

  disjoint R x
  disjoint S x
  disjoint T x
  disjoint ph x
  disjoint F x
  disjoint G x
  disjoint H x
  disjoint a b
  disjoint a c
  disjoint H a
  disjoint b c
  disjoint H b
  disjoint H c
  disjoint R a
  disjoint R b
  disjoint R c
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint T a
  disjoint T b
  disjoint T c
  disjoint a ph
  disjoint b ph
  disjoint c ph
  assert |- ( ph -> H e. ( R MblFnM ( S sX T ) ) )

  proof
    wph
    cH
    cR
    cS
    cT
    csx
    co
    #
    cmbfm
    co
    wcel
    cR
    cuni
    #
    @0
    cuni
    #
    cH
    wf
    cH
    ccnv
    #
    vc
    cv
    #
    cima
    #
    cR
    wcel
    #
    vc
    va
    vb
    cS
    cT
    va
    cv
    #
    vb
    cv
    #
    cxp
    #
    cmpt2
    #
    crn
    #
    wral
    wph
    vx
    @1
    vx
    cv
    #
    cF
    cfv
    #
    @12
    cG
    cfv
    #
    cop
    #
    @2
    cH
    wph
    @12
    @1
    wcel
    #
    wa
    #
    @15
    cS
    cuni
    #
    cT
    cuni
    #
    cxp
    #
    @2
    @17
    @13
    @18
    wcel
    @14
    @19
    wcel
    @15
    @20
    wcel
    wph
    @1
    @18
    @12
    cF
    wph
    cR
    cS
    cF
    mbfmco.1
    mbfmco.2
    mbfmco2.4
    mbfmf
    #
    ffvelrnda
    wph
    @1
    @19
    @12
    cG
    wph
    cR
    cT
    cG
    mbfmco.1
    mbfmco.3
    mbfmco2.5
    mbfmf
    #
    ffvelrnda
    @13
    @14
    @18
    @19
    opelxpi
    syl2anc
    wph
    @20
    @2
    wceq
    #
    @16
    wph
    cS
    csiga
    crn
    cuni
    #
    wcel
    #
    cT
    @24
    wcel
    #
    @23
    mbfmco.2
    mbfmco.3
    cS
    cT
    sxuni
    syl2anc
    adantr
    eleqtrd
    mbfmco2.6
    fmptd
    wph
    @6
    vc
    @11
    @4
    @11
    wcel
    wph
    @4
    @9
    wceq
    #
    vb
    cT
    wrex
    va
    cS
    wrex
    #
    @6
    va
    vb
    cS
    cT
    @9
    @4
    @10
    @10
    eqid
    @7
    @8
    va
    vex
    vb
    vex
    xpex
    elrnmpt2
    wph
    @28
    @6
    wph
    @27
    @6
    va
    vb
    cS
    cT
    wph
    @7
    cS
    wcel
    #
    @8
    cT
    wcel
    #
    wa
    #
    @27
    @6
    wph
    @31
    @27
    w3a
    #
    @5
    @3
    @9
    cima
    #
    cR
    @32
    @4
    @9
    @3
    wph
    @31
    @27
    simp3
    imaeq2d
    @32
    wph
    @29
    @30
    @33
    cR
    wcel
    wph
    @31
    @27
    simp1
    wph
    @29
    @30
    @27
    simp2l
    wph
    @29
    @30
    @27
    simp2r
    wph
    @29
    @30
    w3a
    #
    @33
    cF
    ccnv
    @7
    cima
    #
    cG
    ccnv
    @8
    cima
    #
    cin
    #
    cR
    wph
    @29
    @33
    @37
    wceq
    @30
    wph
    vx
    @1
    @18
    @19
    cF
    cG
    cH
    @7
    @8
    @21
    @22
    mbfmco2.6
    xppreima2
    3ad2ant1
    @34
    cR
    @24
    wcel
    #
    @35
    cR
    wcel
    @36
    cR
    wcel
    @37
    cR
    wcel
    wph
    @29
    @38
    @30
    mbfmco.1
    3ad2ant1
    #
    @34
    @7
    cR
    cS
    cF
    @39
    wph
    @29
    @25
    @30
    mbfmco.2
    3ad2ant1
    wph
    @29
    cF
    cR
    cS
    cmbfm
    co
    wcel
    @30
    mbfmco2.4
    3ad2ant1
    wph
    @29
    @30
    simp2
    mbfmcnvima
    @34
    @8
    cR
    cT
    cG
    @39
    wph
    @29
    @26
    @30
    mbfmco.3
    3ad2ant1
    wph
    @29
    cG
    cR
    cT
    cmbfm
    co
    wcel
    @30
    mbfmco2.5
    3ad2ant1
    wph
    @29
    @30
    simp3
    mbfmcnvima
    @35
    @36
    cR
    inelsiga
    syl3anc
    eqeltrd
    syl3anc
    eqeltrd
    3expia
    rexlimdvva
    imp
    sylan2b
    ralrimiva
    wph
    cR
    @0
    cH
    @11
    vc
    wph
    @25
    @26
    @11
    cvv
    wcel
    mbfmco.2
    mbfmco.3
    va
    vb
    @11
    cS
    cT
    @24
    @24
    @11
    eqid
    #
    txbasex
    syl2anc
    mbfmco.1
    wph
    @25
    @26
    @0
    @11
    csigagen
    cfv
    wceq
    mbfmco.2
    mbfmco.3
    va
    vb
    @11
    cS
    cT
    @24
    @24
    @40
    sxval
    syl2anc
    imambfm
    mpbir2and
end
