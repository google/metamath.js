include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cfa.mm"
include "cfv.mm"
include "cmin.mm"
include "cmul.mm"
include "cdiv.mm"
include "cbc.mm"
include "caddc.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "wceq.mm"
include "cn0.mm"
include "cn.mm"
include "cuz.mm"
include "elfzuz2.mm"
include "nnuz.mm"
include "syl6eleqr.mm"
include "nnnn0d.mm"
include "faccl.mm"
include "syl.mm"
include "nncnd.mm"
include "fznn0sub.mm"
include "nn0p1nn.mm"
include "elfznn.mm"
include "nnm1nn0.mm"
include "3syl.mm"
include "nnmulcld.mm"
include "nncn.mm"
include "nnne0.mm"
include "jca.mm"
include "nnne0d.mm"
include "divmuldiv.mm"
include "syl22anc.mm"
include "elfzel2.mm"
include "zcnd.mm"
include "1cnd.mm"
include "subsubd.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "facp1.mm"
include "eqcomd.mm"
include "facnn2.mm"
include "mul32d.mm"
include "mulassd.mm"
include "3eqtr4d.mm"
include "mulcomd.mm"
include "divcan5d.mm"
include "3eqtrrd.mm"
include "0p1e1.mm"
include "oveq1i.mm"
include "cz.mm"
include "wss.mm"
include "0z.mm"
include "fzp1ss.mm"
include "ax-mp.mm"
include "eqsstr3i.mm"
include "sseli.mm"
include "bcval2.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "peano2zm.mm"
include "uzid.mm"
include "peano2uz.mm"
include "4syl.mm"
include "eqeltrrd.mm"
include "fzss2.mm"
include "elfzmlbm.mm"
include "sseldd.mm"

theorem bcm1k
  let cK: class K
  let cN: class N


  assert |- ( K e. ( 1 ... N ) -> ( N _C K ) = ( ( N _C ( K - 1 ) ) x. ( ( N - ( K - 1 ) ) / K ) ) )

  proof
    cK
    c1
    cN
    cfz
    co
    #
    wcel
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
    @2
    cN
    cK
    c1
    cmin
    co
    #
    cmin
    co
    #
    cfa
    cfv
    #
    @8
    cfa
    cfv
    #
    cmul
    co
    #
    cdiv
    co
    #
    @9
    cK
    cdiv
    co
    #
    cmul
    co
    #
    cN
    cK
    cbc
    co
    #
    cN
    @8
    cbc
    co
    #
    @14
    cmul
    co
    @1
    @15
    @2
    @3
    c1
    caddc
    co
    #
    cmul
    co
    #
    @6
    @18
    cmul
    co
    #
    cdiv
    co
    #
    @18
    @2
    cmul
    co
    #
    @18
    @6
    cmul
    co
    #
    cdiv
    co
    @7
    @1
    @2
    @18
    cfa
    cfv
    #
    @11
    cmul
    co
    #
    cdiv
    co
    #
    @18
    cK
    cdiv
    co
    #
    cmul
    co
    #
    @19
    @25
    cK
    cmul
    co
    #
    cdiv
    co
    #
    @15
    @21
    @1
    @2
    cc
    wcel
    @18
    cc
    wcel
    @25
    cc
    wcel
    #
    @25
    cc0
    wne
    #
    wa
    #
    cK
    cc
    wcel
    #
    cK
    cc0
    wne
    #
    wa
    @28
    @30
    wceq
    @1
    @2
    @1
    cN
    cn0
    wcel
    @2
    cn
    wcel
    @1
    cN
    @1
    cN
    c1
    cuz
    cfv
    cn
    cK
    c1
    cN
    elfzuz2
    nnuz
    syl6eleqr
    nnnn0d
    cN
    faccl
    syl
    nncnd
    #
    @1
    @18
    @1
    @3
    cn0
    wcel
    #
    @18
    cn
    wcel
    cK
    c1
    cN
    fznn0sub
    #
    @3
    nn0p1nn
    syl
    #
    nncnd
    #
    @1
    @25
    cn
    wcel
    #
    @33
    @1
    @24
    @11
    @1
    @18
    cn0
    wcel
    @24
    cn
    wcel
    @1
    @18
    @39
    nnnn0d
    @18
    faccl
    syl
    #
    @1
    cK
    cn
    wcel
    #
    @8
    cn0
    wcel
    @11
    cn
    wcel
    cK
    cN
    elfznn
    #
    cK
    nnm1nn0
    @8
    faccl
    3syl
    #
    nnmulcld
    @41
    @31
    @32
    @25
    nncn
    @25
    nnne0
    jca
    syl
    @1
    @34
    @35
    @1
    cK
    @44
    nncnd
    #
    @1
    cK
    @44
    nnne0d
    jca
    @2
    @18
    @25
    cK
    divmuldiv
    syl22anc
    @1
    @13
    @26
    @14
    @27
    cmul
    @1
    @12
    @25
    @2
    cdiv
    @1
    @10
    @24
    @11
    cmul
    @1
    @9
    @18
    cfa
    @1
    cN
    cK
    c1
    @1
    cN
    cK
    c1
    cN
    elfzel2
    #
    zcnd
    #
    @46
    @1
    1cnd
    subsubd
    #
    fveq2d
    oveq1d
    oveq2d
    @1
    @9
    @18
    cK
    cdiv
    @49
    oveq1d
    oveq12d
    @1
    @20
    @29
    @19
    cdiv
    @1
    @4
    @18
    cmul
    co
    #
    @5
    cmul
    co
    @24
    @11
    cK
    cmul
    co
    #
    cmul
    co
    @20
    @29
    @1
    @50
    @24
    @5
    @51
    cmul
    @1
    @24
    @50
    @1
    @37
    @24
    @50
    wceq
    @38
    @3
    facp1
    syl
    eqcomd
    @1
    @43
    @5
    @51
    wceq
    @44
    cK
    facnn2
    syl
    oveq12d
    @1
    @4
    @5
    @18
    @1
    @4
    @1
    @37
    @4
    cn
    wcel
    @38
    @3
    faccl
    syl
    #
    nncnd
    @1
    @5
    @1
    cK
    cn0
    wcel
    @5
    cn
    wcel
    @1
    cK
    @44
    nnnn0d
    cK
    faccl
    syl
    #
    nncnd
    @40
    mul32d
    @1
    @24
    @11
    cK
    @1
    @24
    @42
    nncnd
    @1
    @11
    @45
    nncnd
    @46
    mulassd
    3eqtr4d
    oveq2d
    3eqtr4d
    @1
    @19
    @22
    @20
    @23
    cdiv
    @1
    @2
    @18
    @36
    @40
    mulcomd
    @1
    @6
    @18
    @1
    @6
    @1
    @4
    @5
    @52
    @53
    nnmulcld
    #
    nncnd
    #
    @40
    mulcomd
    oveq12d
    @1
    @2
    @6
    @18
    @36
    @55
    @40
    @1
    @6
    @54
    nnne0d
    @1
    @18
    @39
    nnne0d
    divcan5d
    3eqtrrd
    @1
    cK
    cc0
    cN
    cfz
    co
    #
    wcel
    @16
    @7
    wceq
    @0
    @56
    cK
    @0
    cc0
    c1
    caddc
    co
    #
    cN
    cfz
    co
    #
    @56
    @57
    c1
    cN
    cfz
    0p1e1
    oveq1i
    cc0
    cz
    wcel
    @58
    @56
    wss
    0z
    cc0
    cN
    fzp1ss
    ax-mp
    eqsstr3i
    sseli
    cK
    cN
    bcval2
    syl
    @1
    @17
    @13
    @14
    cmul
    @1
    @8
    @56
    wcel
    @17
    @13
    wceq
    @1
    cc0
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    @56
    @8
    @1
    cN
    @59
    cuz
    cfv
    #
    wcel
    @60
    @56
    wss
    @1
    @59
    c1
    caddc
    co
    #
    cN
    @61
    @1
    cN
    cc
    wcel
    c1
    cc
    wcel
    @62
    cN
    wceq
    @48
    ax-1cn
    cN
    c1
    npcan
    sylancl
    @1
    cN
    cz
    wcel
    @59
    cz
    wcel
    @59
    @61
    wcel
    @62
    @61
    wcel
    @47
    cN
    peano2zm
    @59
    uzid
    @59
    @59
    peano2uz
    4syl
    eqeltrrd
    @59
    cc0
    cN
    fzss2
    syl
    cK
    c1
    cN
    elfzmlbm
    sseldd
    @8
    cN
    bcval2
    syl
    oveq1d
    3eqtr4d
end
