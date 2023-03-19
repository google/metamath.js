include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "cns.mm"
include "cfv.mm"
include "wceq.mm"
include "cc.mm"
include "neg1cn.mm"
include "eqid.mm"
include "nvdi.mm"
include "mp3anr1.mm"
include "3adant2.mm"
include "oveq2d.mm"
include "nvscl.mm"
include "mp3an2.mm"
include "anim12dan.mm"
include "nvadd4.mm"
include "syld3an3.mm"
include "eqtrd.mm"
include "simp1.mm"
include "nvgcl.mm"
include "3expb.mm"
include "3adant3.mm"
include "nvmval.mm"
include "syl3anc.mm"
include "3adant3r.mm"
include "3adant2r.mm"
include "3adant3l.mm"
include "3adant2l.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"

theorem nvaddsub4
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cU: class U
  let cG: class G
  let cM: class M
  let cX: class X
  assume nvpncan2.1: |- X = ( BaseSet ` U )
  assume nvpncan2.2: |- G = ( +v ` U )
  assume nvpncan2.3: |- M = ( -v ` U )


  assert |- ( ( U e. NrmCVec /\ ( A e. X /\ B e. X ) /\ ( C e. X /\ D e. X ) ) -> ( ( A G B ) M ( C G D ) ) = ( ( A M C ) G ( B M D ) ) )

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
    wa
    #
    cC
    cX
    wcel
    #
    cD
    cX
    wcel
    #
    wa
    #
    w3a
    #
    cA
    cB
    cG
    co
    #
    c1
    cneg
    #
    cC
    cD
    cG
    co
    #
    cU
    cns
    cfv
    #
    co
    #
    cG
    co
    #
    cA
    @9
    cC
    @11
    co
    #
    cG
    co
    #
    cB
    @9
    cD
    @11
    co
    #
    cG
    co
    #
    cG
    co
    #
    @8
    @10
    cM
    co
    #
    cA
    cC
    cM
    co
    #
    cB
    cD
    cM
    co
    #
    cG
    co
    @7
    @13
    @8
    @14
    @16
    cG
    co
    #
    cG
    co
    #
    @18
    @7
    @12
    @22
    @8
    cG
    @0
    @6
    @12
    @22
    wceq
    #
    @3
    @0
    @9
    cc
    wcel
    #
    @4
    @5
    @24
    neg1cn
    @9
    cC
    cD
    @11
    cU
    cG
    cX
    nvpncan2.1
    nvpncan2.2
    @11
    eqid
    #
    nvdi
    mp3anr1
    3adant2
    oveq2d
    @0
    @3
    @6
    @14
    cX
    wcel
    #
    @16
    cX
    wcel
    #
    wa
    #
    @23
    @18
    wceq
    @0
    @6
    @29
    @3
    @0
    @4
    @27
    @5
    @28
    @0
    @25
    @4
    @27
    neg1cn
    @9
    cC
    @11
    cU
    cX
    nvpncan2.1
    @26
    nvscl
    mp3an2
    @0
    @25
    @5
    @28
    neg1cn
    @9
    cD
    @11
    cU
    cX
    nvpncan2.1
    @26
    nvscl
    mp3an2
    anim12dan
    3adant2
    cA
    cB
    @14
    @16
    cU
    cG
    cX
    nvpncan2.1
    nvpncan2.2
    nvadd4
    syld3an3
    eqtrd
    @7
    @0
    @8
    cX
    wcel
    #
    @10
    cX
    wcel
    #
    @19
    @13
    wceq
    @0
    @3
    @6
    simp1
    @0
    @3
    @30
    @6
    @0
    @1
    @2
    @30
    cA
    cB
    cU
    cG
    cX
    nvpncan2.1
    nvpncan2.2
    nvgcl
    3expb
    3adant3
    @0
    @6
    @31
    @3
    @0
    @4
    @5
    @31
    cC
    cD
    cU
    cG
    cX
    nvpncan2.1
    nvpncan2.2
    nvgcl
    3expb
    3adant2
    @8
    @10
    @11
    cU
    cG
    cM
    cX
    nvpncan2.1
    nvpncan2.2
    @26
    nvpncan2.3
    nvmval
    syl3anc
    @7
    @20
    @15
    @21
    @17
    cG
    @0
    @1
    @6
    @20
    @15
    wceq
    #
    @2
    @0
    @1
    @4
    @32
    @5
    cA
    cC
    @11
    cU
    cG
    cM
    cX
    nvpncan2.1
    nvpncan2.2
    @26
    nvpncan2.3
    nvmval
    3adant3r
    3adant2r
    @0
    @2
    @6
    @21
    @17
    wceq
    #
    @1
    @0
    @2
    @5
    @33
    @4
    cB
    cD
    @11
    cU
    cG
    cM
    cX
    nvpncan2.1
    nvpncan2.2
    @26
    nvpncan2.3
    nvmval
    3adant3l
    3adant2l
    oveq12d
    3eqtr4d
end
