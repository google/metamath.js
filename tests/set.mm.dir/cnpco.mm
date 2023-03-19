include "ccnp.mm"
include "co.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "ctop.mm"
include "cuni.mm"
include "w3a.mm"
include "ccom.mm"
include "wf.mm"
include "cv.mm"
include "cima.mm"
include "wss.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "cnptop1.mm"
include "adantr.mm"
include "cnptop2.mm"
include "adantl.mm"
include "eqid.mm"
include "cnprcl.mm"
include "3jca.mm"
include "cnpf.mm"
include "fco.mm"
include "syl2anc.mm"
include "simplr.mm"
include "simprl.mm"
include "wceq.mm"
include "fvco3.mm"
include "simprr.mm"
include "eqeltrrd.mm"
include "cnpimaex.mm"
include "syl3anc.mm"
include "simplll.mm"
include "simprrl.mm"
include "imaco.mm"
include "imass2.mm"
include "syl5eqss.mm"
include "simprrr.mm"
include "sstr2.mm"
include "syl2imc.mm"
include "anim2d.mm"
include "reximdv.mm"
include "mpd.mm"
include "rexlimddv.mm"
include "expr.mm"
include "ralrimiva.mm"
include "jca.mm"
include "iscnp2.mm"
include "sylanbrc.mm"

theorem cnpco
  let cP: class P
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cL: class L
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( F e. ( ( J CnP K ) ` P ) /\ G e. ( ( K CnP L ) ` ( F ` P ) ) ) -> ( G o. F ) e. ( ( J CnP L ) ` P ) )

  proof
    cF
    cP
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    cG
    cP
    cF
    cfv
    #
    cK
    cL
    ccnp
    co
    cfv
    wcel
    #
    wa
    #
    cJ
    ctop
    wcel
    #
    cL
    ctop
    wcel
    #
    cP
    cJ
    cuni
    #
    wcel
    #
    w3a
    @6
    cL
    cuni
    #
    cG
    cF
    ccom
    #
    wf
    #
    cP
    @9
    cfv
    #
    vz
    cv
    #
    wcel
    #
    cP
    vx
    cv
    #
    wcel
    #
    @9
    @14
    cima
    #
    @12
    wss
    #
    wa
    #
    vx
    cJ
    wrex
    #
    wi
    #
    vz
    cL
    wral
    #
    wa
    @9
    cP
    cJ
    cL
    ccnp
    co
    cfv
    wcel
    @3
    @4
    @5
    @7
    @0
    @4
    @2
    cP
    cF
    cJ
    cK
    cnptop1
    adantr
    @2
    @5
    @0
    @1
    cG
    cK
    cL
    cnptop2
    adantl
    @0
    @7
    @2
    cP
    cF
    cJ
    cK
    @6
    @6
    eqid
    #
    cnprcl
    adantr
    #
    3jca
    @3
    @10
    @21
    @3
    cK
    cuni
    #
    @8
    cG
    wf
    #
    @6
    @24
    cF
    wf
    #
    @10
    @2
    @25
    @0
    @1
    cG
    cK
    cL
    @24
    @8
    @24
    eqid
    #
    @8
    eqid
    #
    cnpf
    adantl
    @0
    @26
    @2
    cP
    cF
    cJ
    cK
    @6
    @24
    @22
    @27
    cnpf
    adantr
    #
    @6
    @24
    @8
    cG
    cF
    fco
    syl2anc
    @3
    @20
    vz
    cL
    @3
    @12
    cL
    wcel
    #
    @13
    @19
    @3
    @30
    @13
    wa
    #
    wa
    #
    @1
    vy
    cv
    #
    wcel
    #
    cG
    @33
    cima
    #
    @12
    wss
    #
    wa
    #
    @19
    vy
    cK
    @32
    @2
    @30
    @1
    cG
    cfv
    #
    @12
    wcel
    @37
    vy
    cK
    wrex
    @0
    @2
    @31
    simplr
    @3
    @30
    @13
    simprl
    @32
    @11
    @38
    @12
    @3
    @11
    @38
    wceq
    #
    @31
    @3
    @26
    @7
    @39
    @29
    @23
    @6
    @24
    cP
    cG
    cF
    fvco3
    syl2anc
    adantr
    @3
    @30
    @13
    simprr
    eqeltrrd
    vy
    @12
    @1
    cG
    cK
    cL
    cnpimaex
    syl3anc
    @32
    @33
    cK
    wcel
    #
    @37
    wa
    #
    wa
    #
    @15
    cF
    @14
    cima
    #
    @33
    wss
    #
    wa
    #
    vx
    cJ
    wrex
    #
    @19
    @42
    @0
    @40
    @34
    @46
    @0
    @2
    @31
    @41
    simplll
    @32
    @40
    @37
    simprl
    @32
    @40
    @34
    @36
    simprrl
    vx
    @33
    cP
    cF
    cJ
    cK
    cnpimaex
    syl3anc
    @42
    @45
    @18
    vx
    cJ
    @42
    @44
    @17
    @15
    @44
    @16
    @35
    wss
    @42
    @36
    @17
    @44
    @16
    cG
    @43
    cima
    @35
    cG
    cF
    @14
    imaco
    @43
    @33
    cG
    imass2
    syl5eqss
    @32
    @40
    @34
    @36
    simprrr
    @16
    @35
    @12
    sstr2
    syl2imc
    anim2d
    reximdv
    mpd
    rexlimddv
    expr
    ralrimiva
    jca
    vx
    vz
    cP
    @9
    cJ
    cL
    @6
    @8
    @22
    @28
    iscnp2
    sylanbrc
end
