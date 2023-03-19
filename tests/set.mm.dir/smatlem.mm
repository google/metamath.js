include "co.mm"
include "cop.mm"
include "cn.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "cif.mm"
include "cmpt2.mm"
include "cfv.mm"
include "ccom.mm"
include "csmat.mm"
include "wcel.mm"
include "cfz.mm"
include "cxp.mm"
include "cmap.mm"
include "wceq.mm"
include "fz1ssnn.mm"
include "sseldi.mm"
include "smatfval.mm"
include "syl3anc.mm"
include "syl5eq.mm"
include "oveqd.mm"
include "df-ov.mm"
include "syl6eq.mm"
include "cdm.mm"
include "wa.mm"
include "jca.mm"
include "opelxp.mm"
include "sylibr.mm"
include "eqid.mm"
include "opex.mm"
include "dmmpt2.mm"
include "syl6eleqr.mm"
include "wfun.mm"
include "mpt2fun.mm"
include "fvco.mm"
include "mpan.mm"
include "syl.mm"
include "eqtrd.mm"
include "breq1.mm"
include "id.mm"
include "oveq1.mm"
include "ifbieq12d.mm"
include "opeq1d.mm"
include "opeq2d.mm"
include "ovmpt2.mm"
include "opeq12d.mm"
include "syl5eqr.mm"
include "fveq2d.mm"
include "syl6eqr.mm"

theorem smatlem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let cI: class I
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vl: setvar l
  let vm: setvar m
  let cV: class V
  let vx: setvar x
  assume smat.s: |- S = ( K ( subMat1 ` A ) L )
  assume smat.m: |- ( ph -> M e. NN )
  assume smat.n: |- ( ph -> N e. NN )
  assume smat.k: |- ( ph -> K e. ( 1 ... M ) )
  assume smat.l: |- ( ph -> L e. ( 1 ... N ) )
  assume smat.a: |- ( ph -> A e. ( B ^m ( ( 1 ... M ) X. ( 1 ... N ) ) ) )
  assume smatlem.i: |- ( ph -> I e. NN )
  assume smatlem.j: |- ( ph -> J e. NN )
  assume smatlem.1: |- ( ph -> if ( I < K , I , ( I + 1 ) ) = X )
  assume smatlem.2: |- ( ph -> if ( J < L , J , ( J + 1 ) ) = Y )


  assert |- ( ph -> ( I S J ) = ( X A Y ) )

  proof
    wph
    cI
    cJ
    cS
    co
    #
    cI
    cJ
    cop
    #
    vi
    vj
    cn
    cn
    vi
    cv
    #
    cK
    clt
    wbr
    #
    @2
    @2
    c1
    caddc
    co
    #
    cif
    #
    vj
    cv
    #
    cL
    clt
    wbr
    #
    @6
    @6
    c1
    caddc
    co
    #
    cif
    #
    cop
    #
    cmpt2
    #
    cfv
    #
    cA
    cfv
    #
    cX
    cY
    cA
    co
    #
    wph
    @0
    @1
    cA
    @11
    ccom
    #
    cfv
    #
    @13
    wph
    @0
    cI
    cJ
    @15
    co
    @16
    wph
    cS
    @15
    cI
    cJ
    wph
    cS
    cK
    cL
    cA
    csmat
    cfv
    co
    #
    @15
    smat.s
    wph
    cK
    cn
    wcel
    cL
    cn
    wcel
    cA
    cB
    c1
    cM
    cfz
    co
    #
    c1
    cN
    cfz
    co
    #
    cxp
    cmap
    co
    #
    wcel
    @17
    @15
    wceq
    wph
    @18
    cn
    cK
    cM
    fz1ssnn
    smat.k
    sseldi
    wph
    @19
    cn
    cL
    cN
    fz1ssnn
    smat.l
    sseldi
    smat.a
    vi
    vj
    cK
    cL
    cA
    @20
    smatfval
    syl3anc
    syl5eq
    oveqd
    cI
    cJ
    @15
    df-ov
    syl6eq
    wph
    @1
    @11
    cdm
    #
    wcel
    #
    @16
    @13
    wceq
    #
    wph
    @1
    cn
    cn
    cxp
    #
    @21
    wph
    cI
    cn
    wcel
    #
    cJ
    cn
    wcel
    #
    wa
    #
    @1
    @24
    wcel
    wph
    @25
    @26
    smatlem.i
    smatlem.j
    jca
    #
    cI
    cJ
    cn
    cn
    opelxp
    sylibr
    vi
    vj
    cn
    cn
    @10
    @11
    @11
    eqid
    #
    @5
    @9
    opex
    dmmpt2
    syl6eleqr
    @11
    wfun
    @22
    @23
    vi
    vj
    cn
    cn
    @10
    @11
    @29
    mpt2fun
    @1
    cA
    @11
    fvco
    mpan
    syl
    eqtrd
    wph
    @13
    cX
    cY
    cop
    #
    cA
    cfv
    @14
    wph
    @12
    @30
    cA
    wph
    @12
    cI
    cJ
    @11
    co
    #
    @30
    cI
    cJ
    @11
    df-ov
    wph
    @31
    cI
    cK
    clt
    wbr
    #
    cI
    cI
    c1
    caddc
    co
    #
    cif
    #
    cJ
    cL
    clt
    wbr
    #
    cJ
    cJ
    c1
    caddc
    co
    #
    cif
    #
    cop
    #
    @30
    wph
    @27
    @31
    @38
    wceq
    @28
    vi
    vj
    cI
    cJ
    cn
    cn
    @10
    @38
    @11
    @34
    @9
    cop
    @2
    cI
    wceq
    #
    @5
    @34
    @9
    @39
    @3
    @32
    @2
    @4
    cI
    @33
    @2
    cI
    cK
    clt
    breq1
    @39
    id
    @2
    cI
    c1
    caddc
    oveq1
    ifbieq12d
    opeq1d
    @6
    cJ
    wceq
    #
    @9
    @37
    @34
    @40
    @7
    @35
    @6
    @8
    cJ
    @36
    @6
    cJ
    cL
    clt
    breq1
    @40
    id
    @6
    cJ
    c1
    caddc
    oveq1
    ifbieq12d
    opeq2d
    @29
    @34
    @37
    opex
    ovmpt2
    syl
    wph
    @34
    cX
    @37
    cY
    smatlem.1
    smatlem.2
    opeq12d
    eqtrd
    syl5eqr
    fveq2d
    cX
    cY
    cA
    df-ov
    syl6eqr
    eqtrd
end
