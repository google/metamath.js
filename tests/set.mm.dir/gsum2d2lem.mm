include "cmpt2.mm"
include "cfsupp.mm"
include "wbr.mm"
include "wfun.mm"
include "csupp.mm"
include "co.mm"
include "cfn.mm"
include "wcel.mm"
include "eqid.mm"
include "mpt2fun.mm"
include "a1i.mm"
include "wss.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "wral.mm"
include "wf.mm"
include "ralrimivva.mm"
include "fmpt2x.mm"
include "sylib.mm"
include "cdif.mm"
include "wa.mm"
include "cop.mm"
include "wceq.mm"
include "wex.mm"
include "cfv.mm"
include "wrel.mm"
include "relxp.mm"
include "rgenw.mm"
include "reliun.mm"
include "mpbir.mm"
include "eldifi.mm"
include "adantl.mm"
include "elrel.mm"
include "sylancr.mm"
include "nfv.mm"
include "nfiu1.mm"
include "nfcv.mm"
include "nfdif.mm"
include "nfcri.mm"
include "nfan.mm"
include "nfmpt21.mm"
include "nffv.mm"
include "nfeq1.mm"
include "nfmpt22.mm"
include "simprr.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "simprl.mm"
include "eqeltrrd.mm"
include "eldifad.mm"
include "opeliunxp.mm"
include "simpld.mm"
include "simprd.mm"
include "syldan.mm"
include "ovmpt4g.mm"
include "syl3anc.mm"
include "syl5eqr.mm"
include "wn.mm"
include "eldifn.mm"
include "ad2antrl.mm"
include "eleq1d.mm"
include "df-br.mm"
include "syl6bbr.mm"
include "mtbid.mm"
include "jca.mm"
include "3eqtrd.mm"
include "expr.mm"
include "exlimd.mm"
include "mpd.mm"
include "suppss.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "cvv.mm"
include "wb.mm"
include "ralrimiva.mm"
include "mpt2exxg.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "isfsupp.mm"
include "mpbir2and.mm"

theorem gsum2d2lem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let vj: setvar j
  let vk: setvar k
  let cG: class G
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D
  let cE: class E
  assume gsum2d2.b: |- B = ( Base ` G )
  assume gsum2d2.z: |- .0. = ( 0g ` G )
  assume gsum2d2.g: |- ( ph -> G e. CMnd )
  assume gsum2d2.a: |- ( ph -> A e. V )
  assume gsum2d2.r: |- ( ( ph /\ j e. A ) -> C e. W )
  assume gsum2d2.f: |- ( ( ph /\ ( j e. A /\ k e. C ) ) -> X e. B )
  assume gsum2d2.u: |- ( ph -> U e. Fin )
  assume gsum2d2.n: |- ( ( ph /\ ( ( j e. A /\ k e. C ) /\ -. j U k ) ) -> X = .0. )

  disjoint j k
  disjoint B j
  disjoint B k
  disjoint j ph
  disjoint k ph
  disjoint A j
  disjoint A k
  disjoint G j
  disjoint G k
  disjoint U j
  disjoint U k
  disjoint C k
  disjoint V j
  disjoint .0. j
  disjoint .0. k
  disjoint j m
  disjoint j n
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint B m
  disjoint B n
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint D j
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint D k
  disjoint x y
  disjoint x z
  disjoint D x
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint E j
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint m ph
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint A m
  disjoint A n
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint G m
  disjoint G n
  disjoint G x
  disjoint U z
  disjoint X m
  disjoint X n
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint C m
  disjoint C n
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint .0. m
  disjoint .0. n
  disjoint .0. x
  disjoint .0. z
  assert |- ( ph -> ( j e. A , k e. C |-> X ) finSupp .0. )

  proof
    wph
    vj
    vk
    cA
    cC
    cX
    cmpt2
    #
    c.0
    cfsupp
    wbr
    #
    @0
    wfun
    #
    @0
    c.0
    csupp
    co
    #
    cfn
    wcel
    #
    @2
    wph
    vj
    vk
    cA
    cC
    cX
    @0
    @0
    eqid
    #
    mpt2fun
    a1i
    wph
    cU
    cfn
    wcel
    @3
    cU
    wss
    @4
    gsum2d2.u
    wph
    vj
    cA
    vj
    cv
    #
    csn
    #
    cC
    cxp
    #
    ciun
    #
    cB
    vz
    @0
    cU
    c.0
    wph
    cX
    cB
    wcel
    #
    vk
    cC
    wral
    vj
    cA
    wral
    @9
    cB
    @0
    wf
    wph
    @10
    vj
    vk
    cA
    cC
    gsum2d2.f
    ralrimivva
    vj
    vk
    cA
    cC
    cX
    cB
    @0
    @5
    fmpt2x
    sylib
    wph
    vz
    cv
    #
    @9
    cU
    cdif
    #
    wcel
    #
    wa
    #
    @11
    @6
    vk
    cv
    #
    cop
    #
    wceq
    #
    vk
    wex
    #
    vj
    wex
    #
    @11
    @0
    cfv
    #
    c.0
    wceq
    #
    @14
    @9
    wrel
    #
    @11
    @9
    wcel
    #
    @19
    @22
    @8
    wrel
    #
    vj
    cA
    wral
    @24
    vj
    cA
    @7
    cC
    relxp
    rgenw
    vj
    cA
    @8
    reliun
    mpbir
    @13
    @23
    wph
    @11
    @9
    cU
    eldifi
    adantl
    vj
    vk
    @11
    @9
    elrel
    sylancr
    @14
    @18
    @21
    vj
    wph
    @13
    vj
    wph
    vj
    nfv
    vj
    vz
    @12
    vj
    @9
    cU
    vj
    cA
    @8
    nfiu1
    vj
    cU
    nfcv
    nfdif
    nfcri
    nfan
    vj
    @20
    c.0
    vj
    @11
    @0
    vj
    vk
    cA
    cC
    cX
    nfmpt21
    vj
    @11
    nfcv
    nffv
    nfeq1
    @14
    @17
    @21
    vk
    @14
    vk
    nfv
    vk
    @20
    c.0
    vk
    @11
    @0
    vj
    vk
    cA
    cC
    cX
    nfmpt22
    vk
    @11
    nfcv
    nffv
    nfeq1
    wph
    @13
    @17
    @21
    wph
    @13
    @17
    wa
    #
    wa
    #
    @20
    @16
    @0
    cfv
    #
    cX
    c.0
    @26
    @11
    @16
    @0
    wph
    @13
    @17
    simprr
    #
    fveq2d
    @26
    @27
    @6
    @15
    @0
    co
    #
    cX
    @6
    @15
    @0
    df-ov
    @26
    @6
    cA
    wcel
    #
    @15
    cC
    wcel
    #
    @10
    @29
    cX
    wceq
    @26
    @30
    @31
    @26
    @16
    @9
    wcel
    @30
    @31
    wa
    #
    @26
    @16
    @9
    cU
    @26
    @11
    @16
    @12
    @28
    wph
    @13
    @17
    simprl
    eqeltrrd
    eldifad
    vj
    cA
    cC
    @15
    opeliunxp
    sylib
    #
    simpld
    @26
    @30
    @31
    @33
    simprd
    wph
    @25
    @32
    @10
    @33
    gsum2d2.f
    syldan
    vj
    vk
    cA
    cC
    cX
    @0
    cB
    @5
    ovmpt4g
    syl3anc
    syl5eqr
    wph
    @25
    @32
    @6
    @15
    cU
    wbr
    #
    wn
    #
    wa
    cX
    c.0
    wceq
    @26
    @32
    @35
    @33
    @26
    @11
    cU
    wcel
    #
    @34
    @13
    @36
    wn
    wph
    @17
    @11
    @9
    cU
    eldifn
    ad2antrl
    @26
    @36
    @16
    cU
    wcel
    @34
    @26
    @11
    @16
    cU
    @28
    eleq1d
    @6
    @15
    cU
    df-br
    syl6bbr
    mtbid
    jca
    gsum2d2.n
    syldan
    3eqtrd
    expr
    exlimd
    exlimd
    mpd
    suppss
    cU
    @3
    ssfi
    syl2anc
    wph
    @0
    cvv
    wcel
    #
    c.0
    cvv
    wcel
    #
    @1
    @2
    @4
    wa
    wb
    wph
    cA
    cV
    wcel
    cC
    cW
    wcel
    #
    vj
    cA
    wral
    @37
    gsum2d2.a
    wph
    @39
    vj
    cA
    gsum2d2.r
    ralrimiva
    vj
    vk
    cA
    cC
    cX
    cV
    cW
    @0
    @5
    mpt2exxg
    syl2anc
    @38
    wph
    c.0
    cG
    c0g
    cfv
    cvv
    gsum2d2.z
    cG
    c0g
    fvex
    eqeltri
    a1i
    @0
    cvv
    cvv
    c.0
    isfsupp
    syl2anc
    mpbir2and
end
