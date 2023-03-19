include "clm.mm"
include "cfv.mm"
include "wbr.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "clt.mm"
include "cuz.mm"
include "wral.mm"
include "cn.mm"
include "wrex.mm"
include "crp.mm"
include "wa.mm"
include "cc0.mm"
include "cli.mm"
include "c1.mm"
include "cme.mm"
include "cxmt.mm"
include "metxmet.mm"
include "syl.mm"
include "nnuz.mm"
include "1zzd.mm"
include "eqidd.mm"
include "lmmbrf.mm"
include "cabs.mm"
include "cvv.mm"
include "cmpt.mm"
include "nnex.mm"
include "mptex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "cr.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "metcl.mm"
include "syl3anc.mm"
include "recnd.mm"
include "clim0c.mm"
include "wb.mm"
include "eluznn.mm"
include "cle.mm"
include "metge0.mm"
include "absidd.mm"
include "breq1d.mm"
include "sylan2.mm"
include "anassrs.mm"
include "ralbidva.mm"
include "rexbidva.mm"
include "ralbidv.mm"
include "biantrurd.mm"
include "3bitrrd.mm"
include "bitrd.mm"

theorem lmclim2
  let wph: wff ph
  let vx: setvar x
  let cD: class D
  let cF: class F
  let cG: class G
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let vm: setvar m
  let cA: class A
  let cB: class B
  assume lmclim2.2: |- ( ph -> D e. ( Met ` X ) )
  assume lmclim2.3: |- ( ph -> F : NN --> X )
  assume lmclim2.4: |- J = ( MetOpen ` D )
  assume lmclim2.5: |- G = ( x e. NN |-> ( ( F ` x ) D Y ) )
  assume lmclim2.6: |- ( ph -> Y e. X )

  disjoint D x
  disjoint F x
  disjoint G x
  disjoint J x
  disjoint X x
  disjoint ph x
  disjoint Y x
  disjoint j k
  disjoint j n
  disjoint j x
  disjoint D j
  disjoint k n
  disjoint k x
  disjoint D k
  disjoint n x
  disjoint D n
  disjoint F j
  disjoint F k
  disjoint F n
  disjoint G j
  disjoint G k
  disjoint X j
  disjoint X k
  disjoint X n
  disjoint j m
  disjoint A j
  disjoint k m
  disjoint A k
  disjoint m n
  disjoint m x
  disjoint A m
  disjoint A n
  disjoint A x
  disjoint B j
  disjoint B k
  disjoint B m
  disjoint B n
  disjoint B x
  disjoint j ph
  disjoint k ph
  disjoint n ph
  disjoint Y j
  disjoint Y k
  assert |- ( ph -> ( F ( ~~>t ` J ) Y <-> G ~~> 0 ) )

  proof
    wph
    cF
    cY
    cJ
    clm
    cfv
    wbr
    cY
    cX
    wcel
    #
    vk
    cv
    #
    cF
    cfv
    #
    cY
    cD
    co
    #
    vx
    cv
    #
    clt
    wbr
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    cn
    wrex
    #
    vx
    crp
    wral
    #
    wa
    #
    cG
    cc0
    cli
    wbr
    #
    wph
    vx
    @2
    cD
    cY
    vj
    vk
    cF
    cJ
    c1
    cX
    cn
    lmclim2.4
    wph
    cD
    cX
    cme
    cfv
    wcel
    #
    cD
    cX
    cxmt
    cfv
    wcel
    lmclim2.2
    cD
    cX
    metxmet
    syl
    nnuz
    wph
    1zzd
    #
    wph
    @1
    cn
    wcel
    #
    wa
    #
    @2
    eqidd
    lmclim2.3
    lmmbrf
    wph
    @12
    @3
    cabs
    cfv
    #
    @4
    clt
    wbr
    #
    vk
    @7
    wral
    #
    vj
    cn
    wrex
    #
    vx
    crp
    wral
    @10
    @11
    wph
    vx
    @3
    vj
    vk
    cG
    c1
    cvv
    cn
    nnuz
    @14
    cG
    cvv
    wcel
    wph
    cG
    vx
    cn
    @4
    cF
    cfv
    #
    cY
    cD
    co
    #
    cmpt
    cvv
    lmclim2.5
    vx
    cn
    @22
    nnex
    mptex
    eqeltri
    a1i
    @15
    @1
    cG
    cfv
    @3
    wceq
    wph
    vx
    @1
    @22
    @3
    cn
    cG
    @4
    @1
    wceq
    @21
    @2
    cY
    cD
    @4
    @1
    cF
    fveq2
    oveq1d
    lmclim2.5
    @2
    cY
    cD
    ovex
    fvmpt
    adantl
    @16
    @3
    @16
    @13
    @2
    cX
    wcel
    #
    @0
    @3
    cr
    wcel
    wph
    @13
    @15
    lmclim2.2
    adantr
    #
    wph
    cn
    cX
    @1
    cF
    lmclim2.3
    ffvelrnda
    #
    wph
    @0
    @15
    lmclim2.6
    adantr
    #
    @2
    cY
    cD
    cX
    metcl
    syl3anc
    #
    recnd
    clim0c
    wph
    @20
    @9
    vx
    crp
    wph
    @19
    @8
    vj
    cn
    wph
    @6
    cn
    wcel
    #
    wa
    @18
    @5
    vk
    @7
    wph
    @28
    @1
    @7
    wcel
    #
    @18
    @5
    wb
    #
    @28
    @29
    wa
    wph
    @15
    @30
    @1
    @6
    eluznn
    @16
    @17
    @3
    @4
    clt
    @16
    @3
    @27
    @16
    @13
    @23
    @0
    cc0
    @3
    cle
    wbr
    @24
    @25
    @26
    @2
    cY
    cD
    cX
    metge0
    syl3anc
    absidd
    breq1d
    sylan2
    anassrs
    ralbidva
    rexbidva
    ralbidv
    wph
    @0
    @10
    lmclim2.6
    biantrurd
    3bitrrd
    bitrd
end
