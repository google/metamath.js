include "cnv.mm"
include "wcel.mm"
include "w3a.mm"
include "c1.mm"
include "cneg.mm"
include "co.mm"
include "cfv.mm"
include "cc.mm"
include "wceq.mm"
include "simp1.mm"
include "neg1cn.mm"
include "a1i.mm"
include "simp3.mm"
include "nvscl.mm"
include "mp3an2.mm"
include "3adant3.mm"
include "nvdi.mm"
include "syl13anc.mm"
include "nvnegneg.mm"
include "oveq2d.mm"
include "3adant2.mm"
include "simp2.mm"
include "nvcom.mm"
include "syl3anc.mm"
include "3eqtrd.mm"
include "fveq2d.mm"
include "nvgcl.mm"
include "nvm1.mm"
include "syl2anc.mm"
include "eqtr3d.mm"

theorem nvdif
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


  assert |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( N ` ( A G ( -u 1 S B ) ) ) = ( N ` ( B G ( -u 1 S A ) ) ) )

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
    cneg
    #
    cB
    @4
    cA
    cS
    co
    #
    cG
    co
    #
    cS
    co
    #
    cN
    cfv
    #
    cA
    @4
    cB
    cS
    co
    #
    cG
    co
    #
    cN
    cfv
    @6
    cN
    cfv
    #
    @3
    @7
    @10
    cN
    @3
    @7
    @9
    @4
    @5
    cS
    co
    #
    cG
    co
    #
    @9
    cA
    cG
    co
    #
    @10
    @3
    @0
    @4
    cc
    wcel
    #
    @2
    @5
    cX
    wcel
    #
    @7
    @13
    wceq
    @0
    @1
    @2
    simp1
    #
    @15
    @3
    neg1cn
    a1i
    @0
    @1
    @2
    simp3
    #
    @0
    @1
    @16
    @2
    @0
    @15
    @1
    @16
    neg1cn
    @4
    cA
    cS
    cU
    cX
    nvdif.1
    nvdif.4
    nvscl
    mp3an2
    3adant3
    #
    @4
    cB
    @5
    cS
    cU
    cG
    cX
    nvdif.1
    nvdif.2
    nvdif.4
    nvdi
    syl13anc
    @3
    @12
    cA
    @9
    cG
    @0
    @1
    @12
    cA
    wceq
    @2
    cA
    cS
    cU
    cX
    nvdif.1
    nvdif.4
    nvnegneg
    3adant3
    oveq2d
    @3
    @0
    @9
    cX
    wcel
    #
    @1
    @14
    @10
    wceq
    @17
    @0
    @2
    @20
    @1
    @0
    @15
    @2
    @20
    neg1cn
    @4
    cB
    cS
    cU
    cX
    nvdif.1
    nvdif.4
    nvscl
    mp3an2
    3adant2
    @0
    @1
    @2
    simp2
    @9
    cA
    cU
    cG
    cX
    nvdif.1
    nvdif.2
    nvcom
    syl3anc
    3eqtrd
    fveq2d
    @3
    @0
    @6
    cX
    wcel
    #
    @8
    @11
    wceq
    @17
    @3
    @0
    @2
    @16
    @21
    @17
    @18
    @19
    cB
    @5
    cU
    cG
    cX
    nvdif.1
    nvdif.2
    nvgcl
    syl3anc
    @6
    cS
    cU
    cN
    cX
    nvdif.1
    nvdif.4
    nvdif.6
    nvm1
    syl2anc
    eqtr3d
end
