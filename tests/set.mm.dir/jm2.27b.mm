include "cv.mm"
include "crmx.mm"
include "co.mm"
include "wceq.mm"
include "crmy.mm"
include "wa.mm"
include "cz.mm"
include "c2.mm"
include "cexp.mm"
include "c1.mm"
include "cmin.mm"
include "cmul.mm"
include "wrex.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cn0.mm"
include "wb.mm"
include "nnzd.mm"
include "rmxycomplete.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "adantr.mm"
include "nn0zd.mm"
include "ad2antrr.mm"
include "ad3antrrr.mm"
include "cn.mm"
include "caddc.mm"
include "cdvds.mm"
include "wbr.mm"
include "cle.mm"
include "simprl.mm"
include "simprrl.mm"
include "simprrr.mm"
include "simplrl.mm"
include "ad2antlr.mm"
include "simprr.mm"
include "jm2.27a.mm"
include "rexlimddv.mm"

theorem jm2.27b
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  assume jm2.27a1: |- ( ph -> A e. ( ZZ>= ` 2 ) )
  assume jm2.27a2: |- ( ph -> B e. NN )
  assume jm2.27a3: |- ( ph -> C e. NN )
  assume jm2.27a4: |- ( ph -> D e. NN0 )
  assume jm2.27a5: |- ( ph -> E e. NN0 )
  assume jm2.27a6: |- ( ph -> F e. NN0 )
  assume jm2.27a7: |- ( ph -> G e. NN0 )
  assume jm2.27a8: |- ( ph -> H e. NN0 )
  assume jm2.27a9: |- ( ph -> I e. NN0 )
  assume jm2.27a10: |- ( ph -> J e. NN0 )
  assume jm2.27a11: |- ( ph -> ( ( D ^ 2 ) - ( ( ( A ^ 2 ) - 1 ) x. ( C ^ 2 ) ) ) = 1 )
  assume jm2.27a12: |- ( ph -> ( ( F ^ 2 ) - ( ( ( A ^ 2 ) - 1 ) x. ( E ^ 2 ) ) ) = 1 )
  assume jm2.27a13: |- ( ph -> G e. ( ZZ>= ` 2 ) )
  assume jm2.27a14: |- ( ph -> ( ( I ^ 2 ) - ( ( ( G ^ 2 ) - 1 ) x. ( H ^ 2 ) ) ) = 1 )
  assume jm2.27a15: |- ( ph -> E = ( ( J + 1 ) x. ( 2 x. ( C ^ 2 ) ) ) )
  assume jm2.27a16: |- ( ph -> F || ( G - A ) )
  assume jm2.27a17: |- ( ph -> ( 2 x. C ) || ( G - 1 ) )
  assume jm2.27a18: |- ( ph -> F || ( H - C ) )
  assume jm2.27a19: |- ( ph -> ( 2 x. C ) || ( H - B ) )
  assume jm2.27a20: |- ( ph -> B <_ C )


  assert |- ( ph -> C = ( A rmY B ) )

  proof
    wph
    cD
    cA
    vp
    cv
    #
    crmx
    co
    wceq
    #
    cC
    cA
    @0
    crmy
    co
    wceq
    #
    wa
    #
    cC
    cA
    cB
    crmy
    co
    wceq
    #
    vp
    cz
    wph
    cD
    c2
    cexp
    co
    cA
    c2
    cexp
    co
    c1
    cmin
    co
    #
    cC
    c2
    cexp
    co
    #
    cmul
    co
    cmin
    co
    c1
    wceq
    #
    @3
    vp
    cz
    wrex
    #
    jm2.27a11
    wph
    cA
    c2
    cuz
    cfv
    #
    wcel
    #
    cD
    cn0
    wcel
    #
    cC
    cz
    wcel
    @7
    @8
    wb
    jm2.27a1
    jm2.27a4
    wph
    cC
    jm2.27a3
    nnzd
    cA
    vp
    cD
    cC
    rmxycomplete
    syl3anc
    mpbid
    wph
    @0
    cz
    wcel
    #
    @3
    wa
    #
    wa
    #
    cF
    cA
    vq
    cv
    #
    crmx
    co
    wceq
    #
    cE
    cA
    @15
    crmy
    co
    wceq
    #
    wa
    #
    @4
    vq
    cz
    @14
    cF
    c2
    cexp
    co
    @5
    cE
    c2
    cexp
    co
    cmul
    co
    cmin
    co
    c1
    wceq
    #
    @18
    vq
    cz
    wrex
    #
    wph
    @19
    @13
    jm2.27a12
    adantr
    @14
    @10
    cF
    cn0
    wcel
    #
    cE
    cz
    wcel
    #
    @19
    @20
    wb
    wph
    @10
    @13
    jm2.27a1
    adantr
    wph
    @21
    @13
    jm2.27a6
    adantr
    wph
    @22
    @13
    wph
    cE
    jm2.27a5
    nn0zd
    adantr
    cA
    vq
    cF
    cE
    rmxycomplete
    syl3anc
    mpbid
    @14
    @15
    cz
    wcel
    #
    @18
    wa
    #
    wa
    #
    cI
    cG
    vr
    cv
    #
    crmx
    co
    wceq
    #
    cH
    cG
    @26
    crmy
    co
    wceq
    #
    wa
    #
    @4
    vr
    cz
    @25
    cI
    c2
    cexp
    co
    cG
    c2
    cexp
    co
    c1
    cmin
    co
    cH
    c2
    cexp
    co
    cmul
    co
    cmin
    co
    c1
    wceq
    #
    @29
    vr
    cz
    wrex
    #
    wph
    @30
    @13
    @24
    jm2.27a14
    ad2antrr
    @25
    cG
    @9
    wcel
    #
    cI
    cn0
    wcel
    #
    cH
    cz
    wcel
    #
    @30
    @31
    wb
    wph
    @32
    @13
    @24
    jm2.27a13
    ad2antrr
    wph
    @33
    @13
    @24
    jm2.27a9
    ad2antrr
    wph
    @34
    @13
    @24
    wph
    cH
    jm2.27a8
    nn0zd
    ad2antrr
    cG
    vr
    cI
    cH
    rmxycomplete
    syl3anc
    mpbid
    @25
    @26
    cz
    wcel
    #
    @29
    wa
    #
    wa
    cA
    cB
    cC
    cD
    @0
    @15
    @26
    cE
    cF
    cG
    cH
    cI
    cJ
    wph
    @10
    @13
    @24
    @36
    jm2.27a1
    ad3antrrr
    wph
    cB
    cn
    wcel
    @13
    @24
    @36
    jm2.27a2
    ad3antrrr
    wph
    cC
    cn
    wcel
    @13
    @24
    @36
    jm2.27a3
    ad3antrrr
    wph
    @11
    @13
    @24
    @36
    jm2.27a4
    ad3antrrr
    wph
    cE
    cn0
    wcel
    @13
    @24
    @36
    jm2.27a5
    ad3antrrr
    wph
    @21
    @13
    @24
    @36
    jm2.27a6
    ad3antrrr
    wph
    cG
    cn0
    wcel
    @13
    @24
    @36
    jm2.27a7
    ad3antrrr
    wph
    cH
    cn0
    wcel
    @13
    @24
    @36
    jm2.27a8
    ad3antrrr
    wph
    @33
    @13
    @24
    @36
    jm2.27a9
    ad3antrrr
    wph
    cJ
    cn0
    wcel
    @13
    @24
    @36
    jm2.27a10
    ad3antrrr
    wph
    @7
    @13
    @24
    @36
    jm2.27a11
    ad3antrrr
    wph
    @19
    @13
    @24
    @36
    jm2.27a12
    ad3antrrr
    wph
    @32
    @13
    @24
    @36
    jm2.27a13
    ad3antrrr
    wph
    @30
    @13
    @24
    @36
    jm2.27a14
    ad3antrrr
    wph
    cE
    cJ
    c1
    caddc
    co
    c2
    @6
    cmul
    co
    cmul
    co
    wceq
    @13
    @24
    @36
    jm2.27a15
    ad3antrrr
    wph
    cF
    cG
    cA
    cmin
    co
    cdvds
    wbr
    @13
    @24
    @36
    jm2.27a16
    ad3antrrr
    wph
    c2
    cC
    cmul
    co
    #
    cG
    c1
    cmin
    co
    cdvds
    wbr
    @13
    @24
    @36
    jm2.27a17
    ad3antrrr
    wph
    cF
    cH
    cC
    cmin
    co
    cdvds
    wbr
    @13
    @24
    @36
    jm2.27a18
    ad3antrrr
    wph
    @37
    cH
    cB
    cmin
    co
    cdvds
    wbr
    @13
    @24
    @36
    jm2.27a19
    ad3antrrr
    wph
    cB
    cC
    cle
    wbr
    @13
    @24
    @36
    jm2.27a20
    ad3antrrr
    @14
    @12
    @24
    @36
    wph
    @12
    @3
    simprl
    ad2antrr
    @14
    @1
    @24
    @36
    wph
    @12
    @1
    @2
    simprrl
    ad2antrr
    @14
    @2
    @24
    @36
    wph
    @12
    @1
    @2
    simprrr
    ad2antrr
    @14
    @23
    @18
    @36
    simplrl
    @24
    @16
    @14
    @36
    @23
    @16
    @17
    simprl
    ad2antlr
    @24
    @17
    @14
    @36
    @23
    @16
    @17
    simprr
    ad2antlr
    @25
    @35
    @29
    simprl
    @25
    @35
    @27
    @28
    simprrl
    @25
    @35
    @27
    @28
    simprrr
    jm2.27a
    rexlimddv
    rexlimddv
    rexlimddv
end
