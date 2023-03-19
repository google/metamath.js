include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "cfa.mm"
include "cfv.mm"
include "cmin.mm"
include "cmul.mm"
include "cdiv.mm"
include "cbc.mm"
include "cn0.mm"
include "wceq.mm"
include "elfz3nn0.mm"
include "facp1.mm"
include "syl.mm"
include "fznn0sub.mm"
include "nn0cnd.mm"
include "1cnd.mm"
include "elfznn0.mm"
include "addsubd.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "oveq1d.mm"
include "faccld.mm"
include "nncnd.mm"
include "cn.mm"
include "nn0p1nn.mm"
include "eqeltrd.mm"
include "mul32d.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "cc.mm"
include "wne.mm"
include "wa.mm"
include "nnmulcld.mm"
include "nncn.mm"
include "nnne0.mm"
include "jca.mm"
include "nnne0d.mm"
include "divmuldiv.mm"
include "syl22anc.mm"
include "eqtr4d.mm"
include "fzelp1.mm"
include "bcval2.mm"

theorem bcp1n
  let cK: class K
  let cN: class N


  assert |- ( K e. ( 0 ... N ) -> ( ( N + 1 ) _C K ) = ( ( N _C K ) x. ( ( N + 1 ) / ( ( N + 1 ) - K ) ) ) )

  proof
    cK
    cc0
    cN
    cfz
    co
    wcel
    #
    cN
    c1
    caddc
    co
    #
    cfa
    cfv
    #
    @1
    cK
    cmin
    co
    #
    cfa
    cfv
    #
    cK
    cfa
    cfv
    #
    cmul
    co
    #
    cdiv
    co
    #
    cN
    cfa
    cfv
    #
    cN
    cK
    cmin
    co
    #
    cfa
    cfv
    #
    @5
    cmul
    co
    #
    cdiv
    co
    #
    @1
    @3
    cdiv
    co
    #
    cmul
    co
    #
    @1
    cK
    cbc
    co
    #
    cN
    cK
    cbc
    co
    #
    @13
    cmul
    co
    @0
    @7
    @8
    @1
    cmul
    co
    #
    @11
    @3
    cmul
    co
    #
    cdiv
    co
    #
    @14
    @0
    @2
    @17
    @6
    @18
    cdiv
    @0
    cN
    cn0
    wcel
    #
    @2
    @17
    wceq
    cK
    cN
    elfz3nn0
    #
    cN
    facp1
    syl
    @0
    @6
    @10
    @3
    cmul
    co
    #
    @5
    cmul
    co
    @18
    @0
    @4
    @22
    @5
    cmul
    @0
    @9
    c1
    caddc
    co
    #
    cfa
    cfv
    #
    @10
    @23
    cmul
    co
    #
    @4
    @22
    @0
    @9
    cn0
    wcel
    #
    @24
    @25
    wceq
    cK
    cc0
    cN
    fznn0sub
    #
    @9
    facp1
    syl
    @0
    @3
    @23
    cfa
    @0
    cN
    c1
    cK
    @0
    cN
    @21
    nn0cnd
    @0
    1cnd
    @0
    cK
    cK
    cN
    elfznn0
    #
    nn0cnd
    addsubd
    #
    fveq2d
    @0
    @3
    @23
    @10
    cmul
    @29
    oveq2d
    3eqtr4d
    oveq1d
    @0
    @10
    @3
    @5
    @0
    @10
    @0
    @9
    @27
    faccld
    #
    nncnd
    @0
    @3
    @0
    @3
    @23
    cn
    @29
    @0
    @26
    @23
    cn
    wcel
    @27
    @9
    nn0p1nn
    syl
    eqeltrd
    #
    nncnd
    #
    @0
    @5
    @0
    cK
    @28
    faccld
    #
    nncnd
    mul32d
    eqtrd
    oveq12d
    @0
    @8
    cc
    wcel
    @1
    cc
    wcel
    @11
    cc
    wcel
    #
    @11
    cc0
    wne
    #
    wa
    #
    @3
    cc
    wcel
    #
    @3
    cc0
    wne
    #
    wa
    @14
    @19
    wceq
    @0
    @8
    @0
    cN
    @21
    faccld
    nncnd
    @0
    @1
    @0
    @20
    @1
    cn
    wcel
    @21
    cN
    nn0p1nn
    syl
    nncnd
    @0
    @11
    cn
    wcel
    #
    @36
    @0
    @10
    @5
    @30
    @33
    nnmulcld
    @39
    @34
    @35
    @11
    nncn
    @11
    nnne0
    jca
    syl
    @0
    @37
    @38
    @32
    @0
    @3
    @31
    nnne0d
    jca
    @8
    @1
    @11
    @3
    divmuldiv
    syl22anc
    eqtr4d
    @0
    cK
    cc0
    @1
    cfz
    co
    wcel
    @15
    @7
    wceq
    cK
    cc0
    cN
    fzelp1
    cK
    @1
    bcval2
    syl
    @0
    @16
    @12
    @13
    cmul
    cK
    cN
    bcval2
    oveq1d
    3eqtr4d
end
