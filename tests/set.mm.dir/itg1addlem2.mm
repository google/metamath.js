include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "cvol.mm"
include "cfv.mm"
include "cif.mm"
include "cr.mm"
include "wcel.mm"
include "wral.mm"
include "cxp.mm"
include "wf.mm"
include "wn.mm"
include "covol.mm"
include "iffalse.mm"
include "adantl.mm"
include "cdm.mm"
include "citg1.mm"
include "i1fima.mm"
include "syl.mm"
include "inmbl.mm"
include "syl2anc.mm"
include "ad2antrr.mm"
include "mblvol.mm"
include "eqtrd.mm"
include "wne.mm"
include "wo.mm"
include "neorian.mm"
include "wss.mm"
include "inss1.mm"
include "a1i.mm"
include "mblss.mm"
include "cdif.mm"
include "simplrl.mm"
include "simpr.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "i1fima2sn.mm"
include "eqeltrrd.mm"
include "ovolsscl.mm"
include "syl3anc.mm"
include "inss2.mm"
include "adantr.mm"
include "simplrr.mm"
include "jaodan.mm"
include "sylan2br.mm"
include "eqeltrd.mm"
include "ex.mm"
include "iftrue.mm"
include "0re.mm"
include "syl6eqel.mm"
include "pm2.61d2.mm"
include "ralrimivva.mm"
include "fmpt2.mm"
include "sylib.mm"

theorem itg1addlem2
  let wph: wff ph
  let vi: setvar i
  let vj: setvar j
  let cF: class F
  let cG: class G
  let cI: class I
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vv: setvar v
  let vx: setvar x
  let cP: class P
  let vu: setvar u
  assume i1fadd.1: |- ( ph -> F e. dom S.1 )
  assume i1fadd.2: |- ( ph -> G e. dom S.1 )
  assume itg1add.3: |- I = ( i e. RR , j e. RR |-> if ( ( i = 0 /\ j = 0 ) , 0 , ( vol ` ( ( `' F " { i } ) i^i ( `' G " { j } ) ) ) ) )

  disjoint i j
  disjoint F i
  disjoint F j
  disjoint G i
  disjoint G j
  disjoint i ph
  disjoint j ph
  disjoint i y
  disjoint i z
  disjoint A i
  disjoint j y
  disjoint j z
  disjoint A j
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B i
  disjoint B j
  disjoint w y
  disjoint I w
  disjoint I y
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint P v
  disjoint w x
  disjoint w z
  disjoint P w
  disjoint x y
  disjoint x z
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint i u
  disjoint i v
  disjoint i w
  disjoint i x
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> I : ( RR X. RR ) --> RR )

  proof
    wph
    vi
    cv
    #
    cc0
    wceq
    vj
    cv
    #
    cc0
    wceq
    wa
    #
    cc0
    cF
    ccnv
    @0
    csn
    #
    cima
    #
    cG
    ccnv
    @1
    csn
    #
    cima
    #
    cin
    #
    cvol
    cfv
    #
    cif
    #
    cr
    wcel
    #
    vj
    cr
    wral
    vi
    cr
    wral
    cr
    cr
    cxp
    cr
    cI
    wf
    wph
    @10
    vi
    vj
    cr
    cr
    wph
    @0
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    wa
    #
    wa
    #
    @2
    @10
    @14
    @2
    wn
    #
    @10
    @14
    @15
    wa
    #
    @9
    @7
    covol
    cfv
    #
    cr
    @16
    @9
    @8
    @17
    @15
    @9
    @8
    wceq
    @14
    @2
    cc0
    @8
    iffalse
    adantl
    @16
    @7
    cvol
    cdm
    #
    wcel
    #
    @8
    @17
    wceq
    wph
    @19
    @13
    @15
    wph
    @4
    @18
    wcel
    #
    @6
    @18
    wcel
    #
    @19
    wph
    cF
    citg1
    cdm
    #
    wcel
    #
    @20
    i1fadd.1
    @3
    cF
    i1fima
    syl
    #
    wph
    cG
    @22
    wcel
    #
    @21
    i1fadd.2
    @5
    cG
    i1fima
    #
    syl
    @4
    @6
    inmbl
    syl2anc
    ad2antrr
    @7
    mblvol
    syl
    eqtrd
    @15
    @14
    @0
    cc0
    wne
    #
    @1
    cc0
    wne
    #
    wo
    @17
    cr
    wcel
    #
    @0
    cc0
    @1
    cc0
    neorian
    @14
    @27
    @29
    @28
    @14
    @27
    wa
    #
    @7
    @4
    wss
    #
    @4
    cr
    wss
    #
    @4
    covol
    cfv
    #
    cr
    wcel
    @29
    @31
    @30
    @4
    @6
    inss1
    a1i
    @30
    @20
    @32
    wph
    @20
    @13
    @27
    @24
    ad2antrr
    #
    @4
    mblss
    syl
    @30
    @4
    cvol
    cfv
    #
    @33
    cr
    @30
    @20
    @35
    @33
    wceq
    @34
    @4
    mblvol
    syl
    @30
    @23
    @0
    cr
    cc0
    csn
    cdif
    #
    wcel
    #
    @35
    cr
    wcel
    wph
    @23
    @13
    @27
    i1fadd.1
    ad2antrr
    @30
    @11
    @27
    @37
    wph
    @11
    @12
    @27
    simplrl
    @14
    @27
    simpr
    @0
    cr
    cc0
    eldifsn
    sylanbrc
    @0
    cr
    cF
    i1fima2sn
    syl2anc
    eqeltrrd
    @7
    @4
    ovolsscl
    syl3anc
    @14
    @28
    wa
    #
    @7
    @6
    wss
    #
    @6
    cr
    wss
    #
    @6
    covol
    cfv
    #
    cr
    wcel
    @29
    @39
    @38
    @4
    @6
    inss2
    a1i
    @38
    @21
    @40
    @14
    @21
    @28
    @14
    @25
    @21
    wph
    @25
    @13
    i1fadd.2
    adantr
    @26
    syl
    adantr
    #
    @6
    mblss
    syl
    @38
    @6
    cvol
    cfv
    #
    @41
    cr
    @38
    @21
    @43
    @41
    wceq
    @42
    @6
    mblvol
    syl
    @38
    @25
    @1
    @36
    wcel
    #
    @43
    cr
    wcel
    wph
    @25
    @13
    @28
    i1fadd.2
    ad2antrr
    @38
    @12
    @28
    @44
    wph
    @11
    @12
    @28
    simplrr
    @14
    @28
    simpr
    @1
    cr
    cc0
    eldifsn
    sylanbrc
    @1
    cr
    cG
    i1fima2sn
    syl2anc
    eqeltrrd
    @7
    @6
    ovolsscl
    syl3anc
    jaodan
    sylan2br
    eqeltrd
    ex
    @2
    @9
    cc0
    cr
    @2
    cc0
    @8
    iftrue
    0re
    syl6eqel
    pm2.61d2
    ralrimivva
    vi
    vj
    cr
    cr
    @9
    cr
    cI
    itg1add.3
    fmpt2
    sylib
end
