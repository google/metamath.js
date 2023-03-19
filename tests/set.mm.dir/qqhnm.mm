include "cnrg.mm"
include "cdr.mm"
include "cin.mm"
include "wcel.mm"
include "cnlm.mm"
include "cchr.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "w3a.mm"
include "cq.mm"
include "wa.mm"
include "cabs.mm"
include "cnumer.mm"
include "cdenom.mm"
include "cdiv.mm"
include "co.mm"
include "cqqh.mm"
include "simpr.mm"
include "qeqnumdivden.mm"
include "fveq2d.mm"
include "syl.mm"
include "cz.mm"
include "qnumcl.mm"
include "zcnd.mm"
include "cn.mm"
include "qdencl.mm"
include "nncnd.mm"
include "wne.mm"
include "nnne0.mm"
include "3syl.mm"
include "absdivd.mm"
include "czrh.mm"
include "cdvr.mm"
include "inss2.mm"
include "simpl1.mm"
include "sseldi.mm"
include "simpl3.mm"
include "cbs.mm"
include "eqid.mm"
include "qqhvval.mm"
include "syl21anc.mm"
include "cnzr.mm"
include "cui.mm"
include "inss1.mm"
include "drngnzr.mm"
include "crg.mm"
include "zring.mm"
include "crh.mm"
include "wf.mm"
include "drngring.mm"
include "zrhrhm.mm"
include "zringbas.mm"
include "rhmf.mm"
include "4syl.mm"
include "ffvelrnd.mm"
include "nnzd.mm"
include "c0g.mm"
include "elzrhunit.mm"
include "syl22anc.mm"
include "nmdvr.mm"
include "simpl2.mm"
include "zhmnrg.mm"
include "zrhnm.mm"
include "syl31anc.mm"
include "oveq12d.mm"
include "3eqtrrd.mm"

theorem qqhnm
  let cQ: class Q
  let cR: class R
  let cN: class N
  let cZ: class Z
  assume qqhnm.n: |- N = ( norm ` R )
  assume qqhnm.z: |- Z = ( ZMod ` R )


  assert |- ( ( ( R e. ( NrmRing i^i DivRing ) /\ Z e. NrmMod /\ ( chr ` R ) = 0 ) /\ Q e. QQ ) -> ( N ` ( ( QQHom ` R ) ` Q ) ) = ( abs ` Q ) )

  proof
    cR
    cnrg
    cdr
    cin
    #
    wcel
    #
    cZ
    cnlm
    wcel
    #
    cR
    cchr
    cfv
    cc0
    wceq
    #
    w3a
    #
    cQ
    cq
    wcel
    #
    wa
    #
    cQ
    cabs
    cfv
    #
    cQ
    cnumer
    cfv
    #
    cQ
    cdenom
    cfv
    #
    cdiv
    co
    #
    cabs
    cfv
    #
    @8
    cabs
    cfv
    #
    @9
    cabs
    cfv
    #
    cdiv
    co
    #
    cQ
    cR
    cqqh
    cfv
    cfv
    #
    cN
    cfv
    #
    @6
    @5
    @7
    @11
    wceq
    @4
    @5
    simpr
    #
    @5
    cQ
    @10
    cabs
    cQ
    qeqnumdivden
    fveq2d
    syl
    @6
    @8
    @9
    @6
    @8
    @6
    @5
    @8
    cz
    wcel
    #
    @17
    cQ
    qnumcl
    syl
    #
    zcnd
    @6
    @9
    @6
    @5
    @9
    cn
    wcel
    #
    @17
    cQ
    qdencl
    #
    syl
    #
    nncnd
    @6
    @5
    @20
    @9
    cc0
    wne
    #
    @17
    @21
    @9
    nnne0
    3syl
    #
    absdivd
    @6
    @16
    @8
    cR
    czrh
    cfv
    #
    cfv
    #
    @9
    @25
    cfv
    #
    cR
    cdvr
    cfv
    #
    co
    #
    cN
    cfv
    #
    @26
    cN
    cfv
    #
    @27
    cN
    cfv
    #
    cdiv
    co
    #
    @14
    @6
    cR
    cdr
    wcel
    #
    @3
    @5
    @16
    @30
    wceq
    @6
    @0
    cdr
    cR
    cnrg
    cdr
    inss2
    @1
    @2
    @3
    @5
    simpl1
    #
    sseldi
    #
    @1
    @2
    @3
    @5
    simpl3
    #
    @17
    @34
    @3
    wa
    @5
    wa
    @15
    @29
    cN
    cR
    cbs
    cfv
    #
    @28
    cQ
    cR
    @25
    @38
    eqid
    #
    @28
    eqid
    #
    @25
    eqid
    #
    qqhvval
    fveq2d
    syl21anc
    @6
    cR
    cnrg
    wcel
    #
    cR
    cnzr
    wcel
    #
    @26
    @38
    wcel
    @27
    cR
    cui
    cfv
    #
    wcel
    #
    @30
    @33
    wceq
    @6
    @0
    cnrg
    cR
    cnrg
    cdr
    inss1
    @35
    sseldi
    #
    @6
    @34
    @43
    @36
    cR
    drngnzr
    syl
    #
    @6
    cz
    @38
    @8
    @25
    @6
    @34
    cR
    crg
    wcel
    @25
    zring
    cR
    crh
    co
    wcel
    cz
    @38
    @25
    wf
    @36
    cR
    drngring
    cR
    @25
    @41
    zrhrhm
    cz
    @38
    zring
    cR
    @25
    zringbas
    @39
    rhmf
    4syl
    @19
    ffvelrnd
    @6
    @34
    @3
    @9
    cz
    wcel
    #
    @23
    @45
    @36
    @37
    @6
    @9
    @22
    nnzd
    #
    @24
    @38
    cR
    @25
    @9
    cR
    c0g
    cfv
    #
    @39
    @41
    @50
    eqid
    elzrhunit
    syl22anc
    @26
    @27
    @28
    cR
    @44
    cN
    @38
    @39
    qqhnm.n
    @44
    eqid
    @40
    nmdvr
    syl22anc
    @6
    @31
    @12
    @32
    @13
    cdiv
    @6
    @2
    cZ
    cnrg
    wcel
    #
    @43
    @18
    @31
    @12
    wceq
    @1
    @2
    @3
    @5
    simpl2
    #
    @6
    @42
    @51
    @46
    cR
    cZ
    qqhnm.z
    zhmnrg
    syl
    #
    @47
    @19
    @38
    cR
    @25
    @8
    cN
    cZ
    @39
    qqhnm.n
    qqhnm.z
    @41
    zrhnm
    syl31anc
    @6
    @2
    @51
    @43
    @48
    @32
    @13
    wceq
    @52
    @53
    @47
    @49
    @38
    cR
    @25
    @9
    cN
    cZ
    @39
    qqhnm.n
    qqhnm.z
    @41
    zrhnm
    syl31anc
    oveq12d
    3eqtrrd
    3eqtrrd
end
