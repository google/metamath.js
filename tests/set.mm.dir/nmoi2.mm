include "cngp.mm"
include "wcel.mm"
include "cghm.mm"
include "co.mm"
include "w3a.mm"
include "wne.mm"
include "wa.mm"
include "cfv.mm"
include "c1.mm"
include "cdiv.mm"
include "cxmu.mm"
include "cle.mm"
include "cxr.mm"
include "cc0.mm"
include "wbr.mm"
include "cbs.mm"
include "cr.mm"
include "simpl2.mm"
include "wf.mm"
include "simpl3.mm"
include "eqid.mm"
include "ghmf.mm"
include "syl.mm"
include "simprl.mm"
include "ffvelrnd.mm"
include "nmcl.mm"
include "syl2anc.mm"
include "rexrd.mm"
include "nmocl.mm"
include "adantr.mm"
include "crp.mm"
include "nmrpcl.mm"
include "3expb.mm"
include "3ad2antl1.mm"
include "rpxrd.mm"
include "xmulcld.mm"
include "rpreccld.mm"
include "rpge0d.mm"
include "jca.mm"
include "nmoix.mm"
include "adantrr.mm"
include "xlemul1a.mm"
include "syl31anc.mm"
include "cmul.mm"
include "wceq.mm"
include "rpred.mm"
include "rexmul.mm"
include "recnd.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "divrecd.mm"
include "eqtr4d.mm"
include "xmulass.mm"
include "syl3anc.mm"
include "recidd.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "xmulid1.mm"
include "3eqtrd.mm"
include "3brtr3d.mm"

theorem nmoi2
  let cS: class S
  let cT: class T
  let cF: class F
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let cX: class X
  let c.0: class .0.
  let vf: setvar f
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let cA: class A
  let wph: wff ph
  assume nmofval.1: |- N = ( S normOp T )
  assume nmoi.2: |- V = ( Base ` S )
  assume nmoi.3: |- L = ( norm ` S )
  assume nmoi.4: |- M = ( norm ` T )
  assume nmoi2.z: |- .0. = ( 0g ` S )


  assert |- ( ( ( S e. NrmGrp /\ T e. NrmGrp /\ F e. ( S GrpHom T ) ) /\ ( X e. V /\ X =/= .0. ) ) -> ( ( M ` ( F ` X ) ) / ( L ` X ) ) <_ ( N ` F ) )

  proof
    cS
    cngp
    wcel
    #
    cT
    cngp
    wcel
    #
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    w3a
    #
    cX
    cV
    wcel
    #
    cX
    c.0
    wne
    #
    wa
    #
    wa
    #
    cX
    cF
    cfv
    #
    cM
    cfv
    #
    c1
    cX
    cL
    cfv
    #
    cdiv
    co
    #
    cxmu
    co
    #
    cF
    cN
    cfv
    #
    @10
    cxmu
    co
    #
    @11
    cxmu
    co
    #
    @9
    @10
    cdiv
    co
    #
    @13
    cle
    @7
    @9
    cxr
    wcel
    @14
    cxr
    wcel
    @11
    cxr
    wcel
    #
    cc0
    @11
    cle
    wbr
    #
    wa
    @9
    @14
    cle
    wbr
    #
    @12
    @15
    cle
    wbr
    @7
    @9
    @7
    @1
    @8
    cT
    cbs
    cfv
    #
    wcel
    @9
    cr
    wcel
    #
    @0
    @1
    @2
    @6
    simpl2
    @7
    cV
    @20
    cX
    cF
    @7
    @2
    cV
    @20
    cF
    wf
    @0
    @1
    @2
    @6
    simpl3
    cS
    cT
    cF
    cV
    @20
    nmoi.2
    @20
    eqid
    #
    ghmf
    syl
    @3
    @4
    @5
    simprl
    ffvelrnd
    @8
    cT
    cM
    @20
    @22
    nmoi.4
    nmcl
    syl2anc
    #
    rexrd
    @7
    @13
    @10
    @3
    @13
    cxr
    wcel
    #
    @6
    cS
    cT
    cF
    cN
    nmofval.1
    nmocl
    adantr
    #
    @7
    @10
    @0
    @1
    @6
    @10
    crp
    wcel
    #
    @2
    @0
    @4
    @5
    @26
    cX
    cS
    cL
    cV
    c.0
    nmoi.2
    nmoi.3
    nmoi2.z
    nmrpcl
    3expb
    3ad2antl1
    #
    rpxrd
    #
    xmulcld
    @7
    @17
    @18
    @7
    @11
    @7
    @10
    @27
    rpreccld
    #
    rpxrd
    #
    @7
    @11
    @29
    rpge0d
    jca
    @3
    @4
    @19
    @5
    cS
    cT
    cF
    cL
    cM
    cN
    cV
    cX
    nmofval.1
    nmoi.2
    nmoi.3
    nmoi.4
    nmoix
    adantrr
    @9
    @14
    @11
    xlemul1a
    syl31anc
    @7
    @12
    @9
    @11
    cmul
    co
    #
    @16
    @7
    @21
    @11
    cr
    wcel
    #
    @12
    @31
    wceq
    @23
    @7
    @11
    @29
    rpred
    #
    @9
    @11
    rexmul
    syl2anc
    @7
    @9
    @10
    @7
    @9
    @23
    recnd
    @7
    @10
    @27
    rpcnd
    #
    @7
    @10
    @27
    rpne0d
    #
    divrecd
    eqtr4d
    @7
    @15
    @13
    @10
    @11
    cxmu
    co
    #
    cxmu
    co
    #
    @13
    c1
    cxmu
    co
    #
    @13
    @7
    @24
    @10
    cxr
    wcel
    @17
    @15
    @37
    wceq
    @25
    @28
    @30
    @13
    @10
    @11
    xmulass
    syl3anc
    @7
    @36
    c1
    @13
    cxmu
    @7
    @36
    @10
    @11
    cmul
    co
    #
    c1
    @7
    @10
    cr
    wcel
    @32
    @36
    @39
    wceq
    @7
    @10
    @27
    rpred
    @33
    @10
    @11
    rexmul
    syl2anc
    @7
    @10
    @34
    @35
    recidd
    eqtrd
    oveq2d
    @7
    @24
    @38
    @13
    wceq
    @25
    @13
    xmulid1
    syl
    3eqtrd
    3brtr3d
end
