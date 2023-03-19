include "wss.mm"
include "wcel.mm"
include "ccnp.mm"
include "co.mm"
include "cfv.mm"
include "w3a.mm"
include "cres.mm"
include "crest.mm"
include "cuni.mm"
include "wf.mm"
include "cv.mm"
include "cima.mm"
include "wa.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "eqid.mm"
include "cnpf.mm"
include "3ad2ant3.mm"
include "simp1.mm"
include "fssresd.mm"
include "wceq.mm"
include "simpl2.mm"
include "fvres.mm"
include "syl.mm"
include "eleq1d.mm"
include "cnpimaex.mm"
include "3expia.mm"
include "3ad2antl3.mm"
include "cin.mm"
include "idd.mm"
include "simp2.mm"
include "jctird.mm"
include "elin.mm"
include "syl6ibr.mm"
include "inss1.mm"
include "imass2.mm"
include "ax-mp.mm"
include "id.mm"
include "syl5ss.mm"
include "a1i.mm"
include "anim12d.mm"
include "reximdv.mm"
include "cvv.mm"
include "vex.mm"
include "inex1.mm"
include "ctop.mm"
include "wb.mm"
include "cnptop1.mm"
include "uniexg.mm"
include "syl6sseq.mm"
include "ssexd.mm"
include "elrest.mm"
include "syl2anc.mm"
include "simpr.mm"
include "eleq2d.mm"
include "imaeq2d.mm"
include "inss2.mm"
include "resima2.mm"
include "syl6eq.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "rexxfr2d.mm"
include "sylibrd.mm"
include "adantr.mm"
include "syld.mm"
include "sylbid.mm"
include "ralrimiva.mm"
include "ctopon.mm"
include "toptopon.mm"
include "sylib.mm"
include "resttopon.mm"
include "cnptop2.mm"
include "iscnp.mm"
include "syl3anc.mm"
include "mpbir2and.mm"

theorem cnpresti
  let cA: class A
  let cP: class P
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cY: class Y
  assume cnprest.1: |- X = U. J


  assert |- ( ( A C_ X /\ P e. A /\ F e. ( ( J CnP K ) ` P ) ) -> ( F |` A ) e. ( ( ( J |`t A ) CnP K ) ` P ) )

  proof
    cA
    cX
    wss
    #
    cP
    cA
    wcel
    #
    cF
    cP
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    w3a
    #
    cF
    cA
    cres
    #
    cP
    cJ
    cA
    crest
    co
    #
    cK
    ccnp
    co
    cfv
    wcel
    #
    cA
    cK
    cuni
    #
    @4
    wf
    #
    cP
    @4
    cfv
    #
    vy
    cv
    #
    wcel
    #
    cP
    vz
    cv
    #
    wcel
    #
    @4
    @12
    cima
    #
    @10
    wss
    #
    wa
    #
    vz
    @5
    wrex
    #
    wi
    #
    vy
    cK
    wral
    #
    @3
    cX
    @7
    cA
    cF
    @2
    @0
    cX
    @7
    cF
    wf
    @1
    cP
    cF
    cJ
    cK
    cX
    @7
    cnprest.1
    @7
    eqid
    #
    cnpf
    3ad2ant3
    @0
    @1
    @2
    simp1
    #
    fssresd
    @3
    @18
    vy
    cK
    @3
    @10
    cK
    wcel
    #
    wa
    #
    @11
    cP
    cF
    cfv
    #
    @10
    wcel
    #
    @17
    @23
    @9
    @24
    @10
    @23
    @1
    @9
    @24
    wceq
    @0
    @1
    @2
    @22
    simpl2
    cP
    cA
    cF
    fvres
    syl
    eleq1d
    @23
    @25
    cP
    vx
    cv
    #
    wcel
    #
    cF
    @26
    cima
    #
    @10
    wss
    #
    wa
    #
    vx
    cJ
    wrex
    #
    @17
    @2
    @0
    @22
    @25
    @31
    wi
    @1
    @2
    @22
    @25
    @31
    vx
    @10
    cP
    cF
    cJ
    cK
    cnpimaex
    3expia
    3ad2antl3
    @3
    @31
    @17
    wi
    @22
    @3
    @31
    cP
    @26
    cA
    cin
    #
    wcel
    #
    cF
    @32
    cima
    #
    @10
    wss
    #
    wa
    #
    vx
    cJ
    wrex
    @17
    @3
    @30
    @36
    vx
    cJ
    @3
    @27
    @33
    @29
    @35
    @3
    @27
    @27
    @1
    wa
    @33
    @3
    @27
    @27
    @1
    @3
    @27
    idd
    @0
    @1
    @2
    simp2
    #
    jctird
    cP
    @26
    cA
    elin
    syl6ibr
    @29
    @35
    wi
    @3
    @29
    @34
    @28
    @10
    @32
    @26
    wss
    @34
    @28
    wss
    @26
    cA
    inss1
    @32
    @26
    cF
    imass2
    ax-mp
    @29
    id
    syl5ss
    a1i
    anim12d
    reximdv
    @3
    @16
    @36
    vz
    vx
    @32
    @5
    cJ
    cvv
    @32
    cvv
    wcel
    @3
    @26
    cJ
    wcel
    wa
    @26
    cA
    vx
    vex
    inex1
    a1i
    @3
    cJ
    ctop
    wcel
    #
    cA
    cvv
    wcel
    @12
    @5
    wcel
    @12
    @32
    wceq
    #
    vx
    cJ
    wrex
    wb
    @2
    @0
    @38
    @1
    cP
    cF
    cJ
    cK
    cnptop1
    3ad2ant3
    #
    @3
    cA
    cJ
    cuni
    #
    cvv
    @3
    @38
    @41
    cvv
    wcel
    @40
    cJ
    ctop
    uniexg
    syl
    @3
    cA
    cX
    @41
    @21
    cnprest.1
    syl6sseq
    ssexd
    vx
    @12
    cA
    cJ
    ctop
    cvv
    elrest
    syl2anc
    @3
    @39
    wa
    #
    @13
    @33
    @15
    @35
    @42
    @12
    @32
    cP
    @3
    @39
    simpr
    #
    eleq2d
    @42
    @14
    @34
    @10
    @42
    @14
    @4
    @32
    cima
    #
    @34
    @42
    @12
    @32
    @4
    @43
    imaeq2d
    @32
    cA
    wss
    @44
    @34
    wceq
    @26
    cA
    inss2
    cF
    @32
    cA
    resima2
    ax-mp
    syl6eq
    sseq1d
    anbi12d
    rexxfr2d
    sylibrd
    adantr
    syld
    sylbid
    ralrimiva
    @3
    @5
    cA
    ctopon
    cfv
    wcel
    #
    cK
    @7
    ctopon
    cfv
    wcel
    #
    @1
    @6
    @8
    @19
    wa
    wb
    @3
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @0
    @45
    @3
    @38
    @47
    @40
    cJ
    cX
    cnprest.1
    toptopon
    sylib
    @21
    cA
    cJ
    cX
    resttopon
    syl2anc
    @3
    cK
    ctop
    wcel
    #
    @46
    @2
    @0
    @48
    @1
    cP
    cF
    cJ
    cK
    cnptop2
    3ad2ant3
    cK
    @7
    @20
    toptopon
    sylib
    @37
    vz
    vy
    cP
    @4
    @5
    cK
    cA
    @7
    iscnp
    syl3anc
    mpbir2and
end
