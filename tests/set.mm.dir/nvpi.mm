include "cnv.mm"
include "wcel.mm"
include "w3a.mm"
include "c1.mm"
include "ci.mm"
include "co.mm"
include "cfv.mm"
include "cmul.mm"
include "cneg.mm"
include "cr.mm"
include "simp1.mm"
include "cc.mm"
include "ax-icn.mm"
include "nvscl.mm"
include "mp3an2.mm"
include "3adant2.mm"
include "nvgcl.mm"
include "syld3an3.mm"
include "nvcl.mm"
include "syl2anc.mm"
include "recnd.mm"
include "mulid2d.mm"
include "cabs.mm"
include "absnegi.mm"
include "absi.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "wceq.mm"
include "negicn.mm"
include "nvs.mm"
include "simp2.mm"
include "nvdi.mm"
include "mp3anr1.mm"
include "syl12anc.mm"
include "wa.mm"
include "mulneg1i.mm"
include "ixi.mm"
include "negeqi.mm"
include "negneg1e1.mm"
include "nvsass.mm"
include "mpanr1.mm"
include "nvsid.mm"
include "3eqtr3a.mm"
include "oveq2d.mm"
include "3adant3.mm"
include "nvcom.mm"
include "syld3an2.mm"
include "3eqtrd.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "syl5eqr.mm"

theorem nvpi
  let cA: class A
  let cB: class B
  let cS: class S
  let cU: class U
  let cG: class G
  let cN: class N
  let cX: class X
  assume nvdif.1: |- X = ( BaseSet ` U )
  assume nvdif.2: |- G = ( +v ` U )
  assume nvdif.4: |- S = ( .sOLD ` U )
  assume nvdif.6: |- N = ( normCV ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( N ` ( A G ( _i S B ) ) ) = ( N ` ( B G ( -u _i S A ) ) ) )

  proof
    cU
    cnv
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    c1
    cA
    ci
    cB
    cS
    co
    #
    cG
    co
    #
    cN
    cfv
    #
    cmul
    co
    #
    @6
    cB
    ci
    cneg
    #
    cA
    cS
    co
    #
    cG
    co
    #
    cN
    cfv
    #
    @3
    @6
    @3
    @6
    @3
    @0
    @5
    cX
    wcel
    #
    @6
    cr
    wcel
    @0
    @1
    @2
    simp1
    #
    @0
    @1
    @2
    @4
    cX
    wcel
    #
    @12
    @0
    @2
    @14
    @1
    @0
    ci
    cc
    wcel
    #
    @2
    @14
    ax-icn
    ci
    cB
    cS
    cU
    cX
    nvdif.1
    nvdif.4
    nvscl
    mp3an2
    3adant2
    #
    cA
    @4
    cU
    cG
    cX
    nvdif.1
    nvdif.2
    nvgcl
    syld3an3
    #
    @5
    cU
    cN
    cX
    nvdif.1
    nvdif.6
    nvcl
    syl2anc
    recnd
    mulid2d
    @3
    @7
    @8
    cabs
    cfv
    #
    @6
    cmul
    co
    #
    @11
    @18
    c1
    @6
    cmul
    @18
    ci
    cabs
    cfv
    c1
    ci
    ax-icn
    absnegi
    absi
    eqtri
    oveq1i
    @3
    @8
    @5
    cS
    co
    #
    cN
    cfv
    #
    @19
    @11
    @3
    @0
    @12
    @21
    @19
    wceq
    #
    @13
    @17
    @0
    @8
    cc
    wcel
    #
    @12
    @22
    negicn
    @8
    @5
    cS
    cU
    cN
    cX
    nvdif.1
    nvdif.4
    nvdif.6
    nvs
    mp3an2
    syl2anc
    @3
    @20
    @10
    cN
    @3
    @20
    @9
    @8
    @4
    cS
    co
    #
    cG
    co
    #
    @9
    cB
    cG
    co
    #
    @10
    @3
    @0
    @1
    @14
    @20
    @25
    wceq
    #
    @13
    @0
    @1
    @2
    simp2
    @16
    @0
    @23
    @1
    @14
    @27
    negicn
    @8
    cA
    @4
    cS
    cU
    cG
    cX
    nvdif.1
    nvdif.2
    nvdif.4
    nvdi
    mp3anr1
    syl12anc
    @3
    @24
    cB
    @9
    cG
    @0
    @2
    @24
    cB
    wceq
    @1
    @0
    @2
    wa
    @8
    ci
    cmul
    co
    #
    cB
    cS
    co
    #
    c1
    cB
    cS
    co
    @24
    cB
    @28
    c1
    cB
    cS
    @28
    ci
    ci
    cmul
    co
    #
    cneg
    #
    c1
    ci
    ci
    ax-icn
    ax-icn
    mulneg1i
    @31
    c1
    cneg
    #
    cneg
    c1
    @30
    @32
    ixi
    negeqi
    negneg1e1
    eqtri
    eqtri
    oveq1i
    @0
    @15
    @2
    @29
    @24
    wceq
    #
    ax-icn
    @0
    @23
    @15
    @2
    @33
    negicn
    @8
    ci
    cB
    cS
    cU
    cX
    nvdif.1
    nvdif.4
    nvsass
    mp3anr1
    mpanr1
    cB
    cS
    cU
    cX
    nvdif.1
    nvdif.4
    nvsid
    3eqtr3a
    3adant2
    oveq2d
    @0
    @9
    cX
    wcel
    #
    @1
    @2
    @26
    @10
    wceq
    @0
    @1
    @34
    @2
    @0
    @23
    @1
    @34
    negicn
    @8
    cA
    cS
    cU
    cX
    nvdif.1
    nvdif.4
    nvscl
    mp3an2
    3adant3
    @9
    cB
    cU
    cG
    cX
    nvdif.1
    nvdif.2
    nvcom
    syld3an2
    3eqtrd
    fveq2d
    eqtr3d
    syl5eqr
    eqtr3d
end
