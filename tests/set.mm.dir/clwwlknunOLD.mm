include "cusgr.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cclwwlkn.mm"
include "co.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "crab.mm"
include "ciun.mm"
include "wrex.mm"
include "eliun.mm"
include "weq.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "rexbii.mm"
include "wi.mm"
include "simpl.mm"
include "a1i.mm"
include "rexlimdvw.mm"
include "cword.mm"
include "chash.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "cedg.mm"
include "cmin.mm"
include "cfzo.mm"
include "wral.mm"
include "clsw.mm"
include "w3a.mm"
include "eqid.mm"
include "clwwlknp.mm"
include "anim2i.mm"
include "usgrpredgv.mm"
include "ex.mm"
include "simpr.mm"
include "syl6.mm"
include "adantr.mm"
include "com12.mm"
include "3ad2ant3.mm"
include "impcom.mm"
include "eqcomd.mm"
include "biantrud.mm"
include "bicomd.mm"
include "rspcedv.mm"
include "adantld.mm"
include "mpcom.mm"
include "impbid.mm"
include "syl5bb.mm"
include "syl5rbb.mm"
include "eqrdv.mm"

theorem clwwlknunOLD
  let vx: setvar x
  let vw: setvar w
  let cG: class G
  let cN: class N
  let cV: class V
  let vy: setvar y
  let vi: setvar i
  assume clwwlknunOLD.v: |- V = ( Vtx ` G )

  disjoint G x
  disjoint N x
  disjoint V x
  disjoint w x
  disjoint G w
  disjoint N w
  disjoint G y
  disjoint x y
  disjoint N y
  disjoint V y
  disjoint w y
  disjoint G i
  disjoint i x
  disjoint i y
  disjoint N i
  assert |- ( ( G e. USGraph /\ N e. NN0 ) -> ( N ClWWalksN G ) = U_ x e. V { w e. ( N ClWWalksN G ) | ( w ` 0 ) = x } )

  proof
    cG
    cusgr
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    vy
    cN
    cG
    cclwwlkn
    co
    #
    vx
    cV
    cc0
    vw
    cv
    #
    cfv
    #
    vx
    cv
    #
    wceq
    #
    vw
    @3
    crab
    #
    ciun
    #
    vy
    cv
    #
    @9
    wcel
    @10
    @8
    wcel
    #
    vx
    cV
    wrex
    #
    @2
    @10
    @3
    wcel
    #
    vx
    @10
    cV
    @8
    eliun
    @12
    @13
    cc0
    @10
    cfv
    #
    @6
    wceq
    #
    wa
    #
    vx
    cV
    wrex
    #
    @2
    @13
    @11
    @16
    vx
    cV
    @7
    @15
    vw
    @10
    @3
    vw
    vy
    weq
    @5
    @14
    @6
    cc0
    @4
    @10
    fveq1
    eqeq1d
    elrab
    rexbii
    @2
    @17
    @13
    @2
    @16
    @13
    vx
    cV
    @16
    @13
    wi
    @2
    @13
    @15
    simpl
    a1i
    rexlimdvw
    @2
    @13
    @17
    @2
    @10
    cV
    cword
    wcel
    @10
    chash
    cfv
    cN
    wceq
    wa
    #
    vi
    cv
    #
    @10
    cfv
    @19
    c1
    caddc
    co
    @10
    cfv
    cpr
    cG
    cedg
    cfv
    #
    wcel
    vi
    cc0
    cN
    c1
    cmin
    co
    cfzo
    co
    wral
    #
    @10
    clsw
    cfv
    #
    @14
    cpr
    @20
    wcel
    #
    w3a
    #
    wa
    #
    @2
    @13
    wa
    @17
    @13
    @24
    @2
    vi
    @20
    cG
    cN
    cV
    @10
    clwwlknunOLD.v
    @20
    eqid
    #
    clwwlknp
    anim2i
    @25
    @13
    @17
    @2
    @25
    @16
    @13
    vx
    @14
    cV
    @24
    @2
    @14
    cV
    wcel
    #
    @23
    @18
    @2
    @27
    wi
    @21
    @2
    @23
    @27
    @0
    @23
    @27
    wi
    @1
    @0
    @23
    @22
    cV
    wcel
    #
    @27
    wa
    #
    @27
    @0
    @23
    @29
    @20
    cG
    @22
    @14
    cV
    @26
    clwwlknunOLD.v
    usgrpredgv
    ex
    @28
    @27
    simpr
    syl6
    adantr
    com12
    3ad2ant3
    impcom
    @25
    @6
    @14
    wceq
    #
    wa
    #
    @13
    @16
    @31
    @15
    @13
    @31
    @6
    @14
    @25
    @30
    simpr
    eqcomd
    biantrud
    bicomd
    rspcedv
    adantld
    mpcom
    ex
    impbid
    syl5bb
    syl5rbb
    eqrdv
end
