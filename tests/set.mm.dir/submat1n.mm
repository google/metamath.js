include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "cmpt2.mm"
include "cmin.mm"
include "csmat.mm"
include "cfv.mm"
include "csubma.mm"
include "wceq.mm"
include "cuz.mm"
include "fzdif2.mm"
include "nnuz.mm"
include "eleq2s.mm"
include "adantr.mm"
include "cbs.mm"
include "eqid.mm"
include "elfz1end.mm"
include "biimpi.mm"
include "sylibr.mm"
include "syl.mm"
include "cxp.mm"
include "cmap.mm"
include "matbas2i.mm"
include "ad2antlr.mm"
include "cfzo.mm"
include "simprl.mm"
include "cz.mm"
include "nnz.mm"
include "fzoval.mm"
include "eqtr4d.mm"
include "eleqtrrd.mm"
include "simprr.mm"
include "smattl.mm"
include "eqcomd.mm"
include "mpt2eq123dva.mm"
include "simpr.mm"
include "submaval.mm"
include "syl3anc.mm"
include "cmat.mm"
include "smatcl.mm"
include "matmpt2.mm"
include "3eqtr4rd.mm"

theorem submat1n
  let cA: class A
  let cB: class B
  let cR: class R
  let cM: class M
  let cN: class N
  let vi: setvar i
  let vj: setvar j
  assume submat1n.a: |- A = ( ( 1 ... N ) Mat R )
  assume submat1n.b: |- B = ( Base ` A )


  assert |- ( ( N e. NN /\ M e. B ) -> ( N ( subMat1 ` M ) N ) = ( N ( ( ( 1 ... N ) subMat R ) ` M ) N ) )

  proof
    cN
    cn
    wcel
    #
    cM
    cB
    wcel
    #
    wa
    #
    vi
    vj
    c1
    cN
    cfz
    co
    #
    cN
    csn
    cdif
    #
    @4
    vi
    cv
    #
    vj
    cv
    #
    cM
    co
    #
    cmpt2
    #
    vi
    vj
    c1
    cN
    c1
    cmin
    co
    cfz
    co
    #
    @9
    @5
    @6
    cN
    cN
    cM
    csmat
    cfv
    co
    #
    co
    #
    cmpt2
    #
    cN
    cN
    cM
    @3
    cR
    csubma
    co
    #
    cfv
    co
    #
    @10
    @2
    vi
    vj
    @4
    @4
    @7
    @9
    @9
    @11
    @0
    @4
    @9
    wceq
    #
    @1
    @15
    cN
    c1
    cuz
    cfv
    cn
    c1
    cN
    fzdif2
    nnuz
    eleq2s
    #
    adantr
    #
    @2
    @15
    @5
    @4
    wcel
    #
    @17
    adantr
    @2
    @18
    @6
    @4
    wcel
    #
    wa
    #
    wa
    #
    @11
    @7
    @21
    cM
    cR
    cbs
    cfv
    #
    @10
    @5
    @6
    cN
    cN
    cN
    cN
    @10
    eqid
    #
    @2
    @0
    @20
    @2
    cN
    @3
    wcel
    #
    @0
    @0
    @24
    @1
    @0
    @24
    cN
    elfz1end
    #
    biimpi
    #
    adantr
    #
    @25
    sylibr
    #
    adantr
    #
    @29
    @21
    @0
    @24
    @29
    @26
    syl
    #
    @30
    @1
    cM
    @22
    @3
    @3
    cxp
    cmap
    co
    wcel
    @0
    @20
    cA
    cB
    cR
    @22
    cM
    @3
    submat1n.a
    @22
    eqid
    submat1n.b
    matbas2i
    ad2antlr
    @21
    @5
    @4
    c1
    cN
    cfzo
    co
    #
    @2
    @18
    @19
    simprl
    @21
    @0
    @31
    @4
    wceq
    @29
    @0
    @31
    @9
    @4
    @0
    cN
    cz
    wcel
    @31
    @9
    wceq
    cN
    nnz
    c1
    cN
    fzoval
    syl
    @16
    eqtr4d
    syl
    #
    eleqtrrd
    @21
    @6
    @4
    @31
    @2
    @18
    @19
    simprr
    @32
    eleqtrrd
    smattl
    eqcomd
    mpt2eq123dva
    @2
    @1
    @24
    @24
    @14
    @8
    wceq
    @0
    @1
    simpr
    #
    @27
    @27
    cA
    cB
    @13
    cR
    vi
    vj
    cN
    cN
    cM
    @3
    submat1n.a
    @13
    eqid
    submat1n.b
    submaval
    syl3anc
    @2
    @10
    @9
    cR
    cmat
    co
    #
    cbs
    cfv
    #
    wcel
    @10
    @12
    wceq
    @2
    cA
    cB
    @35
    cR
    @10
    cN
    cN
    cM
    cN
    submat1n.a
    submat1n.b
    @35
    eqid
    #
    @23
    @28
    @27
    @27
    @33
    smatcl
    @34
    @35
    cR
    vi
    vj
    @10
    @9
    @34
    eqid
    @36
    matmpt2
    syl
    3eqtr4rd
end
