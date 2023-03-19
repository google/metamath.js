include "cewlks.mm"
include "co.mm"
include "wcel.mm"
include "cxnn0.mm"
include "cle.mm"
include "wbr.mm"
include "cvv.mm"
include "wa.mm"
include "ciedg.mm"
include "cfv.mm"
include "cdm.mm"
include "cword.mm"
include "cv.mm"
include "c1.mm"
include "cmin.mm"
include "cin.mm"
include "chash.mm"
include "cfzo.mm"
include "wral.mm"
include "w3a.mm"
include "wi.mm"
include "eqid.mm"
include "ewlkprop.mm"
include "simpl2.mm"
include "cxr.mm"
include "xnn0xr.mm"
include "adantl.mm"
include "adantr.mm"
include "fvex.mm"
include "inex1.mm"
include "hashxrcl.mm"
include "mp1i.mm"
include "xrletr.mm"
include "syl3anc.mm"
include "exp4b.mm"
include "imp32.mm"
include "ralimdv.mm"
include "ex.mm"
include "com23.mm"
include "a1d.mm"
include "3imp1.mm"
include "wb.mm"
include "simpl1l.mm"
include "simprl.mm"
include "isewlk.mm"
include "mpbir2and.mm"
include "syl.mm"
include "3impib.mm"

theorem ewlkle
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let vk: setvar k


  assert |- ( ( F e. ( G EdgWalks S ) /\ T e. NN0* /\ T <_ S ) -> F e. ( G EdgWalks T ) )

  proof
    cF
    cG
    cS
    cewlks
    co
    wcel
    #
    cT
    cxnn0
    wcel
    #
    cT
    cS
    cle
    wbr
    #
    cF
    cG
    cT
    cewlks
    co
    wcel
    #
    @0
    cG
    cvv
    wcel
    #
    cS
    cxnn0
    wcel
    #
    wa
    #
    cF
    cG
    ciedg
    cfv
    #
    cdm
    cword
    #
    wcel
    #
    cS
    vk
    cv
    #
    c1
    cmin
    co
    cF
    cfv
    #
    @7
    cfv
    #
    @10
    cF
    cfv
    @7
    cfv
    #
    cin
    #
    chash
    cfv
    #
    cle
    wbr
    #
    vk
    c1
    cF
    chash
    cfv
    cfzo
    co
    #
    wral
    #
    w3a
    #
    @1
    @2
    wa
    #
    @3
    wi
    cS
    vk
    cF
    cG
    @7
    @7
    eqid
    #
    ewlkprop
    @19
    @20
    @3
    @19
    @20
    wa
    #
    @3
    @9
    cT
    @15
    cle
    wbr
    #
    vk
    @17
    wral
    #
    @6
    @9
    @18
    @20
    simpl2
    #
    @6
    @9
    @18
    @20
    @24
    @6
    @18
    @20
    @24
    wi
    wi
    @9
    @6
    @20
    @18
    @24
    @6
    @20
    @18
    @24
    wi
    @6
    @20
    wa
    @16
    @23
    vk
    @17
    @6
    @1
    @2
    @16
    @23
    wi
    #
    @5
    @1
    @2
    @26
    wi
    wi
    @4
    @5
    @1
    @2
    @16
    @23
    @5
    @1
    wa
    #
    cT
    cxr
    wcel
    #
    cS
    cxr
    wcel
    #
    @15
    cxr
    wcel
    #
    @2
    @16
    wa
    @23
    wi
    @1
    @28
    @5
    cT
    xnn0xr
    adantl
    @5
    @29
    @1
    cS
    xnn0xr
    adantr
    @14
    cvv
    wcel
    @30
    @27
    @12
    @13
    @11
    @7
    fvex
    inex1
    @14
    cvv
    hashxrcl
    mp1i
    cT
    cS
    @15
    xrletr
    syl3anc
    exp4b
    adantl
    imp32
    ralimdv
    ex
    com23
    a1d
    3imp1
    @22
    @4
    @1
    @9
    @3
    @9
    @24
    wa
    wb
    @4
    @5
    @9
    @18
    @20
    simpl1l
    @19
    @1
    @2
    simprl
    @25
    cT
    @8
    vk
    cF
    cG
    @7
    cvv
    @21
    isewlk
    syl3anc
    mpbir2and
    ex
    syl
    3impib
end
