include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "cco1.mm"
include "c0g.mm"
include "wceq.mm"
include "cn.mm"
include "wral.mm"
include "wa.mm"
include "cpl1.mm"
include "cascl.mm"
include "cc0.mm"
include "cif.mm"
include "eqid.mm"
include "mat2pmatvalel.mm"
include "adantr.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "cn0.mm"
include "cvv.mm"
include "cbs.mm"
include "cmpt.mm"
include "simpl2.mm"
include "simprl.mm"
include "simprr.mm"
include "simpl3.mm"
include "matecld.mm"
include "jca.mm"
include "coe1scl.mm"
include "syl.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "adantl.mm"
include "nnnn0.mm"
include "ovex.mm"
include "fvex.mm"
include "ifex.mm"
include "a1i.mm"
include "fvmptd.mm"
include "wn.mm"
include "nnne0.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "3eqtrd.mm"
include "ralrimiva.mm"
include "ralrimivva.mm"
include "cmat.mm"
include "wb.mm"
include "mat2pmatbas.mm"
include "cpmatel.mm"
include "syld3an3.mm"
include "mpbird.mm"

theorem m2cpm
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let cM: class M
  let cN: class N
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  assume m2cpm.s: |- S = ( N ConstPolyMat R )
  assume m2cpm.t: |- T = ( N matToPolyMat R )
  assume m2cpm.a: |- A = ( N Mat R )
  assume m2cpm.b: |- B = ( Base ` A )


  assert |- ( ( N e. Fin /\ R e. Ring /\ M e. B ) -> ( T ` M ) e. S )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    cM
    cB
    wcel
    #
    w3a
    #
    cM
    cT
    cfv
    #
    cS
    wcel
    #
    vn
    cv
    #
    vi
    cv
    #
    vj
    cv
    #
    @4
    co
    #
    cco1
    cfv
    #
    cfv
    #
    cR
    c0g
    cfv
    #
    wceq
    #
    vn
    cn
    wral
    #
    vj
    cN
    wral
    vi
    cN
    wral
    #
    @3
    @14
    vi
    vj
    cN
    cN
    @3
    @7
    cN
    wcel
    #
    @8
    cN
    wcel
    #
    wa
    #
    wa
    #
    @13
    vn
    cn
    @19
    @6
    cn
    wcel
    #
    wa
    #
    @11
    @6
    @7
    @8
    cM
    co
    #
    cR
    cpl1
    cfv
    #
    cascl
    cfv
    #
    cfv
    #
    cco1
    cfv
    #
    cfv
    @6
    cc0
    wceq
    #
    @22
    @12
    cif
    #
    @12
    @21
    @6
    @10
    @26
    @21
    @9
    @25
    cco1
    @19
    @9
    @25
    wceq
    @20
    cA
    cB
    @23
    cR
    @24
    cT
    cM
    cN
    crg
    @7
    @8
    m2cpm.t
    m2cpm.a
    m2cpm.b
    @23
    eqid
    #
    @24
    eqid
    #
    mat2pmatvalel
    adantr
    fveq2d
    fveq1d
    @21
    vk
    @6
    vk
    cv
    #
    cc0
    wceq
    #
    @22
    @12
    cif
    #
    @28
    cn0
    @26
    cvv
    @21
    @1
    @22
    cR
    cbs
    cfv
    #
    wcel
    #
    wa
    #
    @26
    vk
    cn0
    @33
    cmpt
    wceq
    @19
    @36
    @20
    @19
    @1
    @35
    @0
    @1
    @2
    @18
    simpl2
    @19
    cA
    cB
    cR
    @7
    @8
    @34
    cM
    cN
    m2cpm.a
    @34
    eqid
    #
    m2cpm.b
    @3
    @16
    @17
    simprl
    @3
    @16
    @17
    simprr
    @0
    @1
    @2
    @18
    simpl3
    matecld
    jca
    adantr
    vk
    @24
    @23
    cR
    @34
    @22
    @12
    @29
    @30
    @37
    @12
    eqid
    coe1scl
    syl
    @31
    @6
    wceq
    #
    @33
    @28
    wceq
    @21
    @38
    @32
    @27
    @22
    @12
    @31
    @6
    cc0
    eqeq1
    ifbid
    adantl
    @20
    @6
    cn0
    wcel
    @19
    @6
    nnnn0
    adantl
    @28
    cvv
    wcel
    @21
    @27
    @22
    @12
    @7
    @8
    cM
    ovex
    cR
    c0g
    fvex
    ifex
    a1i
    fvmptd
    @21
    @27
    @22
    @12
    @20
    @27
    wn
    @19
    @20
    @6
    cc0
    @6
    nnne0
    neneqd
    adantl
    iffalsed
    3eqtrd
    ralrimiva
    ralrimivva
    @0
    @1
    @2
    @4
    cN
    @23
    cmat
    co
    #
    cbs
    cfv
    #
    wcel
    @5
    @15
    wb
    cA
    cB
    @39
    @23
    cR
    cT
    cM
    cN
    m2cpm.t
    m2cpm.a
    m2cpm.b
    @29
    @39
    eqid
    #
    mat2pmatbas
    @40
    @39
    @23
    cR
    cS
    vi
    vj
    vn
    @4
    cN
    crg
    m2cpm.s
    @29
    @41
    @40
    eqid
    cpmatel
    syld3an3
    mpbird
end
