include "cnv.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "ccj.mm"
include "cfv.mm"
include "cpv.mm"
include "cnmcv.mm"
include "c2.mm"
include "cexp.mm"
include "c1.mm"
include "cneg.mm"
include "cns.mm"
include "cmin.mm"
include "ci.mm"
include "cmul.mm"
include "caddc.mm"
include "c4.mm"
include "cdiv.mm"
include "eqid.mm"
include "ipval2.mm"
include "fveq2d.mm"
include "wceq.mm"
include "3com23.mm"
include "cc.mm"
include "ipval2lem3.mm"
include "recnd.mm"
include "neg1cn.mm"
include "ipval2lem4.mm"
include "mpan2.mm"
include "subcld.mm"
include "ax-icn.mm"
include "negicn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "addcld.mm"
include "cc0.mm"
include "wne.mm"
include "4cn.mm"
include "4ne0.mm"
include "cjdiv.mm"
include "mp3an23.mm"
include "syl.mm"
include "cr.mm"
include "4re.mm"
include "cjre.mm"
include "ax-mp.mm"
include "oveq2i.mm"
include "ipval2lem2.mm"
include "resubcld.mm"
include "cjreim.mm"
include "syl2anc.mm"
include "submul2.mm"
include "mp3an2.mm"
include "nvcom.mm"
include "oveq1d.mm"
include "nvdif.mm"
include "oveq12d.mm"
include "negsubdi2d.mm"
include "nvpi.mm"
include "eqcomd.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "syl5eq.mm"
include "eqtr4d.mm"

theorem dipcj
  let cA: class A
  let cB: class B
  let cP: class P
  let cU: class U
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume ipcl.1: |- X = ( BaseSet ` U )
  assume ipcl.7: |- P = ( .iOLD ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( * ` ( A P B ) ) = ( B P A ) )

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
    cA
    cB
    cP
    co
    #
    ccj
    cfv
    cA
    cB
    cU
    cpv
    cfv
    #
    co
    #
    cU
    cnmcv
    cfv
    #
    cfv
    #
    c2
    cexp
    co
    #
    cA
    c1
    cneg
    #
    cB
    cU
    cns
    cfv
    #
    co
    @5
    co
    @7
    cfv
    #
    c2
    cexp
    co
    #
    cmin
    co
    #
    ci
    cA
    ci
    cB
    @11
    co
    @5
    co
    @7
    cfv
    #
    c2
    cexp
    co
    #
    cA
    ci
    cneg
    #
    cB
    @11
    co
    @5
    co
    @7
    cfv
    #
    c2
    cexp
    co
    #
    cmin
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    c4
    cdiv
    co
    #
    ccj
    cfv
    #
    cB
    cA
    cP
    co
    #
    @3
    @4
    @23
    ccj
    cA
    cB
    cP
    @11
    cU
    @5
    @7
    cX
    ipcl.1
    @5
    eqid
    #
    @11
    eqid
    #
    @7
    eqid
    #
    ipcl.7
    ipval2
    fveq2d
    @3
    @25
    cB
    cA
    @5
    co
    #
    @7
    cfv
    #
    c2
    cexp
    co
    #
    cB
    @10
    cA
    @11
    co
    @5
    co
    @7
    cfv
    #
    c2
    cexp
    co
    #
    cmin
    co
    #
    ci
    cB
    ci
    cA
    @11
    co
    @5
    co
    @7
    cfv
    #
    c2
    cexp
    co
    #
    cB
    @17
    cA
    @11
    co
    @5
    co
    @7
    cfv
    #
    c2
    cexp
    co
    #
    cmin
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    c4
    cdiv
    co
    #
    @24
    @0
    @2
    @1
    @25
    @42
    wceq
    cB
    cA
    cP
    @11
    cU
    @5
    @7
    cX
    ipcl.1
    @26
    @27
    @28
    ipcl.7
    ipval2
    3com23
    @3
    @24
    @22
    ccj
    cfv
    #
    c4
    ccj
    cfv
    #
    cdiv
    co
    #
    @42
    @3
    @22
    cc
    wcel
    #
    @24
    @45
    wceq
    #
    @3
    @14
    @21
    @3
    @9
    @13
    @3
    @9
    cA
    cB
    cP
    @11
    cU
    @5
    @7
    cX
    ipcl.1
    @26
    @27
    @28
    ipcl.7
    ipval2lem3
    #
    recnd
    @3
    @10
    cc
    wcel
    #
    @13
    cc
    wcel
    neg1cn
    cA
    cB
    @10
    cP
    @11
    cU
    @5
    @7
    cX
    ipcl.1
    @26
    @27
    @28
    ipcl.7
    ipval2lem4
    mpan2
    subcld
    #
    @3
    ci
    cc
    wcel
    #
    @20
    cc
    wcel
    #
    @21
    cc
    wcel
    ax-icn
    @3
    @16
    @19
    @3
    @51
    @16
    cc
    wcel
    ax-icn
    cA
    cB
    ci
    cP
    @11
    cU
    @5
    @7
    cX
    ipcl.1
    @26
    @27
    @28
    ipcl.7
    ipval2lem4
    mpan2
    #
    @3
    @17
    cc
    wcel
    #
    @19
    cc
    wcel
    negicn
    cA
    cB
    @17
    cP
    @11
    cU
    @5
    @7
    cX
    ipcl.1
    @26
    @27
    @28
    ipcl.7
    ipval2lem4
    mpan2
    #
    subcld
    #
    ci
    @20
    mulcl
    sylancr
    addcld
    @46
    c4
    cc
    wcel
    c4
    cc0
    wne
    @47
    4cn
    4ne0
    @22
    c4
    cjdiv
    mp3an23
    syl
    @3
    @45
    @43
    c4
    cdiv
    co
    @42
    @44
    c4
    @43
    cdiv
    c4
    cr
    wcel
    @44
    c4
    wceq
    4re
    c4
    cjre
    ax-mp
    oveq2i
    @3
    @43
    @41
    c4
    cdiv
    @3
    @43
    @14
    @21
    cmin
    co
    #
    @14
    ci
    @20
    cneg
    #
    cmul
    co
    #
    caddc
    co
    #
    @41
    @3
    @14
    cr
    wcel
    @20
    cr
    wcel
    @43
    @57
    wceq
    @3
    @9
    @13
    @48
    @3
    @49
    @13
    cr
    wcel
    neg1cn
    cA
    cB
    @10
    cP
    @11
    cU
    @5
    @7
    cX
    ipcl.1
    @26
    @27
    @28
    ipcl.7
    ipval2lem2
    mpan2
    resubcld
    @3
    @16
    @19
    @3
    @51
    @16
    cr
    wcel
    ax-icn
    cA
    cB
    ci
    cP
    @11
    cU
    @5
    @7
    cX
    ipcl.1
    @26
    @27
    @28
    ipcl.7
    ipval2lem2
    mpan2
    @3
    @54
    @19
    cr
    wcel
    negicn
    cA
    cB
    @17
    cP
    @11
    cU
    @5
    @7
    cX
    ipcl.1
    @26
    @27
    @28
    ipcl.7
    ipval2lem2
    mpan2
    resubcld
    @14
    @20
    cjreim
    syl2anc
    @3
    @14
    cc
    wcel
    #
    @52
    @57
    @60
    wceq
    #
    @50
    @56
    @61
    @51
    @52
    @62
    ax-icn
    @14
    ci
    @20
    submul2
    mp3an2
    syl2anc
    @3
    @14
    @34
    @59
    @40
    caddc
    @3
    @9
    @31
    @13
    @33
    cmin
    @3
    @8
    @30
    c2
    cexp
    @3
    @6
    @29
    @7
    cA
    cB
    cU
    @5
    cX
    ipcl.1
    @26
    nvcom
    fveq2d
    oveq1d
    @3
    @12
    @32
    c2
    cexp
    cA
    cB
    @11
    cU
    @5
    @7
    cX
    ipcl.1
    @26
    @27
    @28
    nvdif
    oveq1d
    oveq12d
    @3
    @58
    @39
    ci
    cmul
    @3
    @58
    @19
    @16
    cmin
    co
    @39
    @3
    @16
    @19
    @53
    @55
    negsubdi2d
    @3
    @19
    @36
    @16
    @38
    cmin
    @3
    @18
    @35
    c2
    cexp
    @3
    @35
    @18
    @0
    @2
    @1
    @35
    @18
    wceq
    cB
    cA
    @11
    cU
    @5
    @7
    cX
    ipcl.1
    @26
    @27
    @28
    nvpi
    3com23
    eqcomd
    oveq1d
    @3
    @15
    @37
    c2
    cexp
    cA
    cB
    @11
    cU
    @5
    @7
    cX
    ipcl.1
    @26
    @27
    @28
    nvpi
    oveq1d
    oveq12d
    eqtrd
    oveq2d
    oveq12d
    3eqtrd
    oveq1d
    syl5eq
    eqtrd
    eqtr4d
    eqtr4d
end
