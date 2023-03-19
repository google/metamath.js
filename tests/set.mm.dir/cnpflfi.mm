include "cflim.mm"
include "co.mm"
include "wcel.mm"
include "ccnp.mm"
include "cfv.mm"
include "wa.mm"
include "cflf.mm"
include "cuni.mm"
include "cv.mm"
include "cima.mm"
include "wss.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "wf.mm"
include "eqid.mm"
include "cnpf.mm"
include "adantl.mm"
include "flimelbas.mm"
include "adantr.mm"
include "ffvelrnd.mm"
include "simplr.mm"
include "simprl.mm"
include "simprr.mm"
include "cnpimaex.mm"
include "syl3anc.mm"
include "anass.mm"
include "simpl.mm"
include "ctopon.mm"
include "cfil.mm"
include "wb.mm"
include "ctop.mm"
include "flimtop.mm"
include "toptopon.mm"
include "sylib.mm"
include "flimfil.mm"
include "flimopn.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simprd.mm"
include "r19.21bi.mm"
include "expimpd.mm"
include "anim1d.mm"
include "syl5bir.mm"
include "reximdv2.mm"
include "mpd.mm"
include "expr.mm"
include "ralrimiva.mm"
include "cnptop2.mm"
include "isflf.mm"
include "mpbir2and.mm"

theorem cnpflfi
  let cA: class A
  let cF: class F
  let cJ: class J
  let cK: class K
  let cL: class L
  let vf: setvar f
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cX: class X
  let cY: class Y


  assert |- ( ( A e. ( J fLim L ) /\ F e. ( ( J CnP K ) ` A ) ) -> ( F ` A ) e. ( ( K fLimf L ) ` F ) )

  proof
    cA
    cJ
    cL
    cflim
    co
    wcel
    #
    cF
    cA
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    wa
    #
    cA
    cF
    cfv
    #
    cF
    cK
    cL
    cflf
    co
    cfv
    wcel
    #
    @3
    cK
    cuni
    #
    wcel
    #
    @3
    vx
    cv
    #
    wcel
    #
    cF
    vy
    cv
    #
    cima
    @7
    wss
    #
    vy
    cL
    wrex
    #
    wi
    #
    vx
    cK
    wral
    #
    @2
    cJ
    cuni
    #
    @5
    cA
    cF
    @1
    @14
    @5
    cF
    wf
    #
    @0
    cA
    cF
    cJ
    cK
    @14
    @5
    @14
    eqid
    #
    @5
    eqid
    #
    cnpf
    adantl
    #
    @0
    cA
    @14
    wcel
    #
    @1
    cA
    cL
    cJ
    @14
    @16
    flimelbas
    adantr
    ffvelrnd
    @2
    @12
    vx
    cK
    @2
    @7
    cK
    wcel
    #
    @8
    @11
    @2
    @20
    @8
    wa
    #
    wa
    #
    cA
    @9
    wcel
    #
    @10
    wa
    #
    vy
    cJ
    wrex
    #
    @11
    @22
    @1
    @20
    @8
    @25
    @0
    @1
    @21
    simplr
    @2
    @20
    @8
    simprl
    @2
    @20
    @8
    simprr
    vy
    @7
    cA
    cF
    cJ
    cK
    cnpimaex
    syl3anc
    @22
    @24
    @10
    vy
    cJ
    cL
    @9
    cJ
    wcel
    #
    @24
    wa
    @26
    @23
    wa
    #
    @10
    wa
    @22
    @9
    cL
    wcel
    #
    @10
    wa
    @26
    @23
    @10
    anass
    @22
    @27
    @28
    @10
    @22
    @26
    @23
    @28
    @22
    @23
    @28
    wi
    #
    vy
    cJ
    @2
    @29
    vy
    cJ
    wral
    #
    @21
    @2
    @19
    @30
    @2
    @0
    @19
    @30
    wa
    #
    @0
    @1
    simpl
    @2
    cJ
    @14
    ctopon
    cfv
    wcel
    #
    cL
    @14
    cfil
    cfv
    wcel
    #
    @0
    @31
    wb
    @2
    cJ
    ctop
    wcel
    #
    @32
    @0
    @34
    @1
    cA
    cL
    cJ
    flimtop
    adantr
    cJ
    @14
    @16
    toptopon
    sylib
    @0
    @33
    @1
    cA
    cL
    cJ
    @14
    @16
    flimfil
    adantr
    #
    vy
    cA
    cL
    cJ
    @14
    flimopn
    syl2anc
    mpbid
    simprd
    adantr
    r19.21bi
    expimpd
    anim1d
    syl5bir
    reximdv2
    mpd
    expr
    ralrimiva
    @2
    cK
    @5
    ctopon
    cfv
    wcel
    #
    @33
    @15
    @4
    @6
    @13
    wa
    wb
    @2
    cK
    ctop
    wcel
    #
    @36
    @1
    @37
    @0
    cA
    cF
    cJ
    cK
    cnptop2
    adantl
    cK
    @5
    @17
    toptopon
    sylib
    @35
    @18
    @3
    vx
    cF
    cK
    cL
    @5
    @14
    vy
    isflf
    syl3anc
    mpbir2and
end
