include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "ccn.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "ccnp.mm"
include "wral.mm"
include "ccnv.mm"
include "cima.mm"
include "iscn.mm"
include "simprbda.mm"
include "cuni.mm"
include "eqid.mm"
include "cncnpi.mm"
include "ralrimiva.mm"
include "adantl.mm"
include "wceq.mm"
include "toponuni.mm"
include "ad2antrr.mm"
include "raleqdv.mm"
include "mpbird.mm"
include "jca.mm"
include "simprl.mm"
include "wss.mm"
include "wrex.mm"
include "wi.mm"
include "cdm.mm"
include "cnvimass.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "ssralv.mm"
include "syl.mm"
include "simprr.mm"
include "simpllr.mm"
include "wfn.mm"
include "ffn.mm"
include "ad2antlr.mm"
include "elpreima.mm"
include "simplbda.mm"
include "syl2anc.mm"
include "cnpimaex.mm"
include "syl3anc.mm"
include "wfun.mm"
include "wb.mm"
include "ffun.mm"
include "simp-4l.mm"
include "toponss.mm"
include "sylan.mm"
include "sseqtr4d.mm"
include "funimass3.mm"
include "anbi2d.mm"
include "rexbidva.mm"
include "mpbid.mm"
include "expr.mm"
include "ralimdva.mm"
include "syld.mm"
include "impr.mm"
include "an32s.mm"
include "ctop.mm"
include "topontop.mm"
include "ad3antrrr.mm"
include "eltop2.mm"
include "adantr.mm"
include "mpbir2and.mm"
include "impbida.mm"

theorem cncnp
  let vx: setvar x
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vu: setvar u
  let vy: setvar y

  disjoint F x
  disjoint J x
  disjoint K x
  disjoint X x
  disjoint Y x
  disjoint u x
  disjoint u y
  disjoint F u
  disjoint x y
  disjoint F y
  disjoint J u
  disjoint J y
  disjoint K u
  disjoint K y
  disjoint X u
  disjoint X y
  disjoint Y u
  disjoint Y y
  assert |- ( ( J e. ( TopOn ` X ) /\ K e. ( TopOn ` Y ) ) -> ( F e. ( J Cn K ) <-> ( F : X --> Y /\ A. x e. X F e. ( ( J CnP K ) ` x ) ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    wa
    #
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    cX
    cY
    cF
    wf
    #
    cF
    vx
    cv
    #
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    vx
    cX
    wral
    #
    wa
    #
    @2
    @3
    wa
    #
    @4
    @7
    @2
    @3
    @4
    cF
    ccnv
    vy
    cv
    #
    cima
    #
    cJ
    wcel
    #
    vy
    cK
    wral
    #
    vy
    cF
    cJ
    cK
    cX
    cY
    iscn
    #
    simprbda
    @9
    @7
    @6
    vx
    cJ
    cuni
    #
    wral
    #
    @3
    @16
    @2
    @3
    @6
    vx
    @15
    @5
    cF
    cJ
    cK
    @15
    @15
    eqid
    cncnpi
    ralrimiva
    adantl
    @9
    @6
    vx
    cX
    @15
    @0
    cX
    @15
    wceq
    @1
    @3
    cX
    cJ
    toponuni
    ad2antrr
    raleqdv
    mpbird
    jca
    @2
    @8
    wa
    #
    @3
    @4
    @13
    @2
    @4
    @7
    simprl
    @17
    @12
    vy
    cK
    @17
    @10
    cK
    wcel
    #
    wa
    #
    @12
    @5
    vu
    cv
    #
    wcel
    #
    @20
    @11
    wss
    #
    wa
    #
    vu
    cJ
    wrex
    #
    vx
    @11
    wral
    #
    @2
    @18
    @8
    @25
    @2
    @18
    wa
    #
    @4
    @7
    @25
    @26
    @4
    wa
    #
    @7
    @6
    vx
    @11
    wral
    #
    @25
    @27
    @11
    cX
    wss
    @7
    @28
    wi
    @27
    cF
    cdm
    #
    @11
    cX
    cF
    @10
    cnvimass
    @4
    @29
    cX
    wceq
    #
    @26
    cX
    cY
    cF
    fdm
    #
    adantl
    syl5sseq
    @6
    vx
    @11
    cX
    ssralv
    syl
    @27
    @6
    @24
    vx
    @11
    @27
    @5
    @11
    wcel
    #
    @6
    @24
    @27
    @32
    @6
    wa
    #
    wa
    #
    @21
    cF
    @20
    cima
    @10
    wss
    #
    wa
    #
    vu
    cJ
    wrex
    #
    @24
    @34
    @6
    @18
    @5
    cF
    cfv
    @10
    wcel
    #
    @37
    @27
    @32
    @6
    simprr
    @2
    @18
    @4
    @33
    simpllr
    @34
    cF
    cX
    wfn
    #
    @32
    @38
    @4
    @39
    @26
    @33
    cX
    cY
    cF
    ffn
    ad2antlr
    @27
    @32
    @6
    simprl
    @39
    @32
    @5
    cX
    wcel
    @38
    cX
    @5
    @10
    cF
    elpreima
    simplbda
    syl2anc
    vu
    @10
    @5
    cF
    cJ
    cK
    cnpimaex
    syl3anc
    @34
    @36
    @23
    vu
    cJ
    @34
    @20
    cJ
    wcel
    #
    wa
    #
    @35
    @22
    @21
    @41
    cF
    wfun
    #
    @20
    @29
    wss
    @35
    @22
    wb
    @41
    @4
    @42
    @26
    @4
    @33
    @40
    simpllr
    #
    cX
    cY
    cF
    ffun
    syl
    @41
    @20
    cX
    @29
    @34
    @0
    @40
    @20
    cX
    wss
    @0
    @1
    @18
    @4
    @33
    simp-4l
    @20
    cJ
    cX
    toponss
    sylan
    @41
    @4
    @30
    @43
    @31
    syl
    sseqtr4d
    @20
    @10
    cF
    funimass3
    syl2anc
    anbi2d
    rexbidva
    mpbid
    expr
    ralimdva
    syld
    impr
    an32s
    @19
    cJ
    ctop
    wcel
    #
    @12
    @25
    wb
    @0
    @44
    @1
    @8
    @18
    cX
    cJ
    topontop
    ad3antrrr
    vx
    vu
    @11
    cJ
    eltop2
    syl
    mpbird
    ralrimiva
    @2
    @3
    @4
    @13
    wa
    wb
    @8
    @14
    adantr
    mpbir2and
    impbida
end
