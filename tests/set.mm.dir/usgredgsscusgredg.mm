include "cusgr.mm"
include "wcel.mm"
include "ccusgr.mm"
include "wa.mm"
include "cv.mm"
include "wne.mm"
include "cpr.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "usgredg.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "iscusgredg.mm"
include "weq.mm"
include "sneq.mm"
include "difeq2d.mm"
include "preq2.mm"
include "eleq1d.mm"
include "raleqbidv.mm"
include "rspcv.mm"
include "simpl.mm"
include "necomd.mm"
include "anim2i.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "preq1.mm"
include "syl.mm"
include "prcom.mm"
include "eqeq2i.mm"
include "eqcom.mm"
include "sylbb.mm"
include "biimpd.mm"
include "ad2antll.mm"
include "syld.mm"
include "syl9.mm"
include "impl.mm"
include "adantld.mm"
include "syl5bi.mm"
include "ex.mm"
include "rexlimivv.mm"
include "impancom.mm"
include "ssrdv.mm"

theorem usgredgsscusgredg
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let ve: setvar e
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  assume fusgrmaxsize.v: |- V = ( Vtx ` G )
  assume fusgrmaxsize.e: |- E = ( Edg ` G )
  assume usgrsscusgra.h: |- V = ( Vtx ` H )
  assume usgrsscusgra.f: |- F = ( Edg ` H )


  assert |- ( ( G e. USGraph /\ H e. ComplUSGraph ) -> E C_ F )

  proof
    cG
    cusgr
    wcel
    #
    cH
    ccusgr
    wcel
    #
    wa
    ve
    cE
    cF
    @0
    ve
    cv
    #
    cE
    wcel
    #
    @1
    @2
    cF
    wcel
    #
    @0
    @3
    wa
    va
    cv
    #
    vb
    cv
    #
    wne
    #
    @2
    @5
    @6
    cpr
    #
    wceq
    #
    wa
    #
    vb
    cV
    wrex
    va
    cV
    wrex
    @1
    @4
    wi
    #
    @2
    cE
    cG
    cV
    va
    vb
    fusgrmaxsize.v
    fusgrmaxsize.e
    usgredg
    @10
    @11
    va
    vb
    cV
    cV
    @5
    cV
    wcel
    #
    @6
    cV
    wcel
    #
    wa
    #
    @10
    @11
    @1
    cH
    cusgr
    wcel
    #
    vn
    cv
    #
    vk
    cv
    #
    cpr
    #
    cF
    wcel
    #
    vn
    cV
    @17
    csn
    #
    cdif
    #
    wral
    #
    vk
    cV
    wral
    #
    wa
    @14
    @10
    wa
    #
    @4
    vk
    vn
    cF
    cH
    cV
    usgrsscusgra.h
    usgrsscusgra.f
    iscusgredg
    @24
    @23
    @4
    @15
    @12
    @13
    @10
    @23
    @4
    wi
    @12
    @23
    @16
    @5
    cpr
    #
    cF
    wcel
    #
    vn
    cV
    @5
    csn
    #
    cdif
    #
    wral
    #
    @13
    @10
    wa
    #
    @4
    @22
    @29
    vk
    @5
    cV
    vk
    va
    weq
    #
    @19
    @26
    vn
    @21
    @28
    @31
    @20
    @27
    cV
    @17
    @5
    sneq
    difeq2d
    @31
    @18
    @25
    cF
    @17
    @5
    @16
    preq2
    eleq1d
    raleqbidv
    rspcv
    @30
    @29
    @6
    @5
    cpr
    #
    cF
    wcel
    #
    @4
    @30
    @6
    @28
    wcel
    #
    @29
    @33
    wi
    @30
    @13
    @6
    @5
    wne
    #
    wa
    @34
    @10
    @35
    @13
    @10
    @5
    @6
    @7
    @9
    simpl
    necomd
    anim2i
    @6
    cV
    @5
    eldifsn
    sylibr
    @26
    @33
    vn
    @6
    @28
    vn
    vb
    weq
    @25
    @32
    cF
    @16
    @6
    @5
    preq1
    eleq1d
    rspcv
    syl
    @9
    @33
    @4
    wi
    @13
    @7
    @9
    @33
    @4
    @9
    @32
    @2
    cF
    @9
    @2
    @32
    wceq
    @32
    @2
    wceq
    @8
    @32
    @2
    @5
    @6
    prcom
    eqeq2i
    @2
    @32
    eqcom
    sylbb
    eleq1d
    biimpd
    ad2antll
    syld
    syl9
    impl
    adantld
    syl5bi
    ex
    rexlimivv
    syl
    impancom
    ssrdv
end
