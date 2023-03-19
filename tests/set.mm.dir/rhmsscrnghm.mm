include "crh.mm"
include "cxp.mm"
include "cres.mm"
include "crngh.mm"
include "cssc.mm"
include "wbr.mm"
include "wss.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "crg.mm"
include "cin.mm"
include "crng.mm"
include "wcel.mm"
include "wi.mm"
include "ringrng.mm"
include "a1i.mm"
include "ssrdv.mm"
include "ssrin.mm"
include "syl.mm"
include "3sstr4d.mm"
include "wa.mm"
include "wceq.mm"
include "ovres.mm"
include "adantl.mm"
include "eleq2d.mm"
include "rhmisrnghm.mm"
include "sseld.mm"
include "anim12d.mm"
include "imp.mm"
include "syl5ibr.mm"
include "sylbid.mm"
include "ralrimivva.mm"
include "cvv.mm"
include "wfn.mm"
include "inss1.mm"
include "syl6eqss.mm"
include "xpss12.mm"
include "syl2anc.mm"
include "wb.mm"
include "rhmfn.mm"
include "fnssresb.mm"
include "mp1i.mm"
include "mpbird.mm"
include "rnghmfn.mm"
include "incom.mm"
include "inex1g.mm"
include "syl5eqel.mm"
include "eqeltrd.mm"
include "isssc.mm"
include "mpbir2and.mm"

theorem rhmsscrnghm
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cU: class U
  let cV: class V
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  let vr: setvar r
  let vk: setvar k
  assume rhmsscrnghm.u: |- ( ph -> U e. V )
  assume rhmsscrnghm.r: |- ( ph -> R = ( Ring i^i U ) )
  assume rhmsscrnghm.s: |- ( ph -> S = ( Rng i^i U ) )


  assert |- ( ph -> ( RingHom |` ( R X. R ) ) C_cat ( RngHomo |` ( S X. S ) ) )

  proof
    wph
    crh
    cR
    cR
    cxp
    #
    cres
    #
    crngh
    cS
    cS
    cxp
    #
    cres
    #
    cssc
    wbr
    cR
    cS
    wss
    vx
    cv
    #
    vy
    cv
    #
    @1
    co
    #
    @4
    @5
    @3
    co
    #
    wss
    #
    vy
    cR
    wral
    vx
    cR
    wral
    wph
    crg
    cU
    cin
    #
    crng
    cU
    cin
    #
    cR
    cS
    wph
    crg
    crng
    wss
    @9
    @10
    wss
    wph
    vr
    crg
    crng
    vr
    cv
    #
    crg
    wcel
    @11
    crng
    wcel
    wi
    wph
    @11
    ringrng
    a1i
    ssrdv
    crg
    crng
    cU
    ssrin
    syl
    rhmsscrnghm.r
    rhmsscrnghm.s
    3sstr4d
    #
    wph
    @8
    vx
    vy
    cR
    cR
    wph
    @4
    cR
    wcel
    #
    @5
    cR
    wcel
    #
    wa
    #
    wa
    #
    vh
    @6
    @7
    @16
    vh
    cv
    #
    @6
    wcel
    @17
    @4
    @5
    crh
    co
    #
    wcel
    #
    @17
    @7
    wcel
    #
    @16
    @6
    @18
    @17
    @15
    @6
    @18
    wceq
    wph
    @4
    @5
    cR
    cR
    crh
    ovres
    adantl
    eleq2d
    @19
    @20
    @16
    @17
    @4
    @5
    crngh
    co
    #
    wcel
    @4
    @5
    @17
    rhmisrnghm
    @16
    @7
    @21
    @17
    @16
    @4
    cS
    wcel
    #
    @5
    cS
    wcel
    #
    wa
    #
    @7
    @21
    wceq
    wph
    @15
    @24
    wph
    @13
    @22
    @14
    @23
    wph
    cR
    cS
    @4
    @12
    sseld
    wph
    cR
    cS
    @5
    @12
    sseld
    anim12d
    imp
    @4
    @5
    cS
    cS
    crngh
    ovres
    syl
    eleq2d
    syl5ibr
    sylbid
    ssrdv
    ralrimivva
    wph
    vx
    vy
    cR
    cS
    @1
    @3
    cvv
    wph
    @1
    @0
    wfn
    #
    @0
    crg
    crg
    cxp
    #
    wss
    #
    wph
    cR
    crg
    wss
    #
    @28
    @27
    wph
    cR
    @9
    crg
    rhmsscrnghm.r
    crg
    cU
    inss1
    syl6eqss
    #
    @29
    cR
    crg
    cR
    crg
    xpss12
    syl2anc
    crh
    @26
    wfn
    @25
    @27
    wb
    wph
    rhmfn
    @26
    @0
    crh
    fnssresb
    mp1i
    mpbird
    wph
    @3
    @2
    wfn
    #
    @2
    crng
    crng
    cxp
    #
    wss
    #
    wph
    cS
    crng
    wss
    #
    @33
    @32
    wph
    cS
    @10
    crng
    rhmsscrnghm.s
    crng
    cU
    inss1
    syl6eqss
    #
    @34
    cS
    crng
    cS
    crng
    xpss12
    syl2anc
    crngh
    @31
    wfn
    @30
    @32
    wb
    wph
    rnghmfn
    @31
    @2
    crngh
    fnssresb
    mp1i
    mpbird
    wph
    cS
    @10
    cvv
    rhmsscrnghm.s
    wph
    cU
    cV
    wcel
    #
    @10
    cvv
    wcel
    rhmsscrnghm.u
    @35
    @10
    cU
    crng
    cin
    cvv
    crng
    cU
    incom
    cU
    crng
    cV
    inex1g
    syl5eqel
    syl
    eqeltrd
    isssc
    mpbir2and
end
