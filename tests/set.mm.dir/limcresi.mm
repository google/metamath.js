include "climc.mm"
include "co.mm"
include "cres.mm"
include "cv.mm"
include "wcel.mm"
include "cc.mm"
include "cdm.mm"
include "cin.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "wss.mm"
include "wa.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "wf.mm"
include "limcrcl.mm"
include "simp1d.mm"
include "simp2d.mm"
include "simp3d.mm"
include "eqid.mm"
include "ellimc2.mm"
include "ibi.mm"
include "wceq.mm"
include "inss2.mm"
include "difss.mm"
include "sstri.mm"
include "resima2.mm"
include "ax-mp.mm"
include "inss1.mm"
include "ssdif.mm"
include "sslin.mm"
include "imass2.mm"
include "mp2b.mm"
include "eqsstri.mm"
include "sstr.mm"
include "mpan.mm"
include "anim2i.mm"
include "reximi.mm"
include "imim2i.mm"
include "ralimi.mm"
include "syl.mm"
include "fresin.mm"
include "syl5ss.mm"
include "mpbird.mm"
include "ssriv.mm"

theorem limcresi
  let cB: class B
  let cC: class C
  let cF: class F
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x


  assert |- ( F limCC B ) C_ ( ( F |` C ) limCC B )

  proof
    vx
    cF
    cB
    climc
    co
    #
    cF
    cC
    cres
    #
    cB
    climc
    co
    #
    vx
    cv
    #
    @0
    wcel
    #
    @3
    @2
    wcel
    @3
    cc
    wcel
    #
    @3
    vu
    cv
    #
    wcel
    #
    cB
    vv
    cv
    #
    wcel
    #
    @1
    @8
    cF
    cdm
    #
    cC
    cin
    #
    cB
    csn
    #
    cdif
    #
    cin
    #
    cima
    #
    @6
    wss
    #
    wa
    #
    vv
    ccnfld
    ctopn
    cfv
    #
    wrex
    #
    wi
    #
    vu
    @18
    wral
    #
    wa
    #
    @4
    @5
    @7
    @9
    cF
    @8
    @10
    @12
    cdif
    #
    cin
    #
    cima
    #
    @6
    wss
    #
    wa
    #
    vv
    @18
    wrex
    #
    wi
    #
    vu
    @18
    wral
    #
    wa
    #
    @22
    @4
    @31
    @4
    vv
    vu
    @10
    cB
    @3
    cF
    @18
    @4
    @10
    cc
    cF
    wf
    #
    @10
    cc
    wss
    #
    cB
    cc
    wcel
    #
    cB
    @3
    cF
    limcrcl
    #
    simp1d
    #
    @4
    @32
    @33
    @34
    @35
    simp2d
    #
    @4
    @32
    @33
    @34
    @35
    simp3d
    #
    @18
    eqid
    #
    ellimc2
    ibi
    @30
    @21
    @5
    @29
    @20
    vu
    @18
    @28
    @19
    @7
    @27
    @17
    vv
    @18
    @26
    @16
    @9
    @15
    @25
    wss
    @26
    @16
    @15
    cF
    @14
    cima
    #
    @25
    @14
    cC
    wss
    @15
    @40
    wceq
    @14
    @13
    cC
    @8
    @13
    inss2
    @13
    @11
    cC
    @11
    @12
    difss
    @10
    cC
    inss2
    sstri
    sstri
    cF
    @14
    cC
    resima2
    ax-mp
    @13
    @23
    wss
    #
    @14
    @24
    wss
    @40
    @25
    wss
    @11
    @10
    wss
    @41
    @10
    cC
    inss1
    #
    @11
    @10
    @12
    ssdif
    ax-mp
    @13
    @23
    @8
    sslin
    @14
    @24
    cF
    imass2
    mp2b
    eqsstri
    @15
    @25
    @6
    sstr
    mpan
    anim2i
    reximi
    imim2i
    ralimi
    anim2i
    syl
    @4
    vv
    vu
    @11
    cB
    @3
    @1
    @18
    @4
    @32
    @11
    cc
    @1
    wf
    @36
    @10
    cc
    cF
    cC
    fresin
    syl
    @4
    @11
    @10
    cc
    @42
    @37
    syl5ss
    @38
    @39
    ellimc2
    mpbird
    ssriv
end
