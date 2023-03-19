include "cv.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cuni.mm"
include "wss.mm"
include "com.mm"
include "cdom.mm"
include "wa.mm"
include "cdm.mm"
include "cpw.mm"
include "crab.mm"
include "cesum.mm"
include "cmpt.mm"
include "crn.mm"
include "wrex.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "wcel.mm"
include "cinf.mm"
include "cxr.mm"
include "cle.mm"
include "rpred.mm"
include "readdcld.mm"
include "rexrd.mm"
include "coms.mm"
include "wf.mm"
include "omsf.mm"
include "syl2anc.mm"
include "feq1i.mm"
include "sylibr.mm"
include "wceq.mm"
include "fdm.mm"
include "syl.mm"
include "unieqd.mm"
include "sseqtr4d.mm"
include "cvv.mm"
include "wb.mm"
include "uniexg.mm"
include "jca.mm"
include "ssexg.mm"
include "elpwg.mm"
include "3syl.mm"
include "mpbird.mm"
include "ffvelrnd.mm"
include "elxrge0.mm"
include "simprbi.mm"
include "rpge0d.mm"
include "addge0d.mm"
include "sylanbrc.mm"
include "fveq1i.mm"
include "omsfval.mm"
include "syl3anc.mm"
include "syl5req.mm"
include "ltaddrpd.mm"
include "eqbrtrd.mm"
include "wor.mm"
include "iccssxr.mm"
include "xrltso.mm"
include "soss.mm"
include "mp2.mm"
include "a1i.mm"
include "wn.mm"
include "wral.mm"
include "wi.mm"
include "omscl.mm"
include "xrge0infss.mm"
include "infglb.mm"
include "mp2and.mm"
include "wex.mm"
include "eqid.mm"
include "esumex.mm"
include "elrnmpti.mm"
include "anbi1i.mm"
include "r19.41v.mm"
include "bitr4i.mm"
include "exbii.mm"
include "df-rex.mm"
include "rexcom4.mm"
include "3bitr4i.mm"
include "breq1.mm"
include "biimpa.mm"
include "exlimiv.mm"
include "reximi.mm"
include "sylbi.mm"

theorem omssubaddlem
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cQ: class Q
  let cR: class R
  let cE: class E
  let cM: class M
  let cV: class V
  let vy: setvar y
  let va: setvar a
  let ve: setvar e
  let vt: setvar t
  let vu: setvar u
  assume oms.m: |- M = ( toOMeas ` R )
  assume oms.o: |- ( ph -> Q e. V )
  assume oms.r: |- ( ph -> R : Q --> ( 0 [,] +oo ) )
  assume omssubaddlem.a: |- ( ph -> A C_ U. Q )
  assume omssubaddlem.m: |- ( ph -> ( M ` A ) e. RR )
  assume omssubaddlem.e: |- ( ph -> E e. RR+ )

  disjoint Q x
  disjoint Q z
  disjoint x z
  disjoint R x
  disjoint R z
  disjoint V x
  disjoint V z
  disjoint ph x
  disjoint ph z
  disjoint A w
  disjoint A x
  disjoint A z
  disjoint w x
  disjoint w z
  disjoint E x
  disjoint M x
  disjoint Q w
  disjoint R w
  disjoint V w
  disjoint Q y
  disjoint x y
  disjoint y z
  disjoint R a
  disjoint R y
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint V y
  disjoint a ph
  disjoint ph y
  disjoint A e
  disjoint A t
  disjoint A u
  disjoint e t
  disjoint e u
  disjoint e w
  disjoint e x
  disjoint e z
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint t z
  disjoint u w
  disjoint u x
  disjoint u z
  disjoint E u
  disjoint M u
  disjoint R e
  disjoint R t
  disjoint R u
  disjoint ph u
  assert |- ( ph -> E. x e. { z e. ~P dom R | ( A C_ U. z /\ z ~<_ _om ) } sum* w e. x ( R ` w ) < ( ( M ` A ) + E ) )

  proof
    wph
    vu
    cv
    #
    cA
    cM
    cfv
    #
    cE
    caddc
    co
    #
    clt
    wbr
    #
    vu
    vx
    cA
    vz
    cv
    #
    cuni
    wss
    @4
    com
    cdom
    wbr
    wa
    vz
    cR
    cdm
    #
    cpw
    crab
    #
    vx
    cv
    #
    vw
    cv
    cR
    cfv
    #
    vw
    cesum
    #
    cmpt
    #
    crn
    #
    wrex
    #
    @9
    @2
    clt
    wbr
    #
    vx
    @6
    wrex
    #
    wph
    @2
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    @11
    @15
    clt
    cinf
    #
    @2
    clt
    wbr
    @12
    wph
    @2
    cxr
    wcel
    cc0
    @2
    cle
    wbr
    @16
    wph
    @2
    wph
    @1
    cE
    omssubaddlem.m
    wph
    cE
    omssubaddlem.e
    rpred
    #
    readdcld
    rexrd
    wph
    @1
    cE
    omssubaddlem.m
    @18
    wph
    @1
    @15
    wcel
    #
    cc0
    @1
    cle
    wbr
    #
    wph
    @5
    cuni
    #
    cpw
    #
    @15
    cA
    cM
    wph
    @22
    @15
    cR
    coms
    cfv
    #
    wf
    #
    @22
    @15
    cM
    wf
    wph
    cQ
    cV
    wcel
    #
    cQ
    @15
    cR
    wf
    #
    @24
    oms.o
    oms.r
    cQ
    cR
    cV
    omsf
    syl2anc
    @22
    @15
    cM
    @23
    oms.m
    feq1i
    sylibr
    wph
    cA
    @22
    wcel
    #
    cA
    @21
    wss
    #
    wph
    cA
    cQ
    cuni
    #
    @21
    omssubaddlem.a
    wph
    @5
    cQ
    wph
    @26
    @5
    cQ
    wceq
    oms.r
    cQ
    @15
    cR
    fdm
    syl
    unieqd
    sseqtr4d
    wph
    cA
    @29
    wss
    #
    @29
    cvv
    wcel
    #
    wa
    cA
    cvv
    wcel
    @27
    @28
    wb
    wph
    @30
    @31
    omssubaddlem.a
    wph
    @25
    @31
    oms.o
    cQ
    cV
    uniexg
    syl
    jca
    cA
    @29
    cvv
    ssexg
    cA
    @21
    cvv
    elpwg
    3syl
    mpbird
    #
    ffvelrnd
    @19
    @1
    cxr
    wcel
    @20
    @1
    elxrge0
    simprbi
    syl
    wph
    cE
    omssubaddlem.e
    rpge0d
    addge0d
    @2
    elxrge0
    sylanbrc
    wph
    @17
    @1
    @2
    clt
    wph
    @1
    cA
    @23
    cfv
    #
    @17
    cA
    cM
    @23
    oms.m
    fveq1i
    wph
    @25
    @26
    @30
    @33
    @17
    wceq
    oms.o
    oms.r
    omssubaddlem.a
    vx
    vw
    vz
    cA
    cQ
    cR
    cV
    omsfval
    syl3anc
    syl5req
    wph
    @1
    cE
    omssubaddlem.m
    omssubaddlem.e
    ltaddrpd
    eqbrtrd
    wph
    ve
    vt
    vu
    @15
    @11
    @2
    clt
    @15
    clt
    wor
    #
    wph
    @15
    cxr
    wss
    cxr
    clt
    wor
    @34
    cc0
    cpnf
    iccssxr
    xrltso
    @15
    cxr
    clt
    soss
    mp2
    a1i
    wph
    @11
    @15
    wss
    #
    vt
    cv
    #
    ve
    cv
    #
    clt
    wbr
    wn
    vt
    @11
    wral
    @37
    @36
    clt
    wbr
    @0
    @36
    clt
    wbr
    vu
    @11
    wrex
    wi
    vt
    @15
    wral
    wa
    ve
    @15
    wrex
    wph
    @25
    @26
    @27
    @35
    oms.o
    oms.r
    @32
    vx
    vw
    vz
    cA
    cQ
    cR
    cV
    omscl
    syl3anc
    ve
    vt
    vu
    @11
    xrge0infss
    syl
    infglb
    mp2and
    @12
    @0
    @9
    wceq
    #
    @3
    wa
    #
    vu
    wex
    #
    vx
    @6
    wrex
    #
    @14
    @0
    @11
    wcel
    #
    @3
    wa
    #
    vu
    wex
    @39
    vx
    @6
    wrex
    #
    vu
    wex
    @12
    @41
    @43
    @44
    vu
    @43
    @38
    vx
    @6
    wrex
    #
    @3
    wa
    @44
    @42
    @45
    @3
    vx
    @6
    @9
    @0
    @10
    @10
    eqid
    @7
    @8
    vw
    esumex
    elrnmpti
    anbi1i
    @38
    @3
    vx
    @6
    r19.41v
    bitr4i
    exbii
    @3
    vu
    @11
    df-rex
    @39
    vx
    vu
    @6
    rexcom4
    3bitr4i
    @40
    @13
    vx
    @6
    @39
    @13
    vu
    @38
    @3
    @13
    @0
    @9
    @2
    clt
    breq1
    biimpa
    exlimiv
    reximi
    sylbi
    syl
end
