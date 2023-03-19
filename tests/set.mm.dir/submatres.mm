include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "csmat.mm"
include "cfv.mm"
include "co.mm"
include "c1.mm"
include "cfz.mm"
include "csubma.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "cmpt2.mm"
include "cmin.mm"
include "cxp.mm"
include "cres.mm"
include "submat1n.mm"
include "wceq.mm"
include "simpr.mm"
include "cuz.mm"
include "nnuz.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "eluzfz2.mm"
include "syl.mm"
include "adantr.mm"
include "eqid.mm"
include "submaval.mm"
include "syl3anc.mm"
include "wss.mm"
include "fzdif2.mm"
include "difss.mm"
include "syl6eqssr.mm"
include "resmpt2.mm"
include "syl2anc.mm"
include "matmpt2.mm"
include "reseq1d.mm"
include "adantl.mm"
include "eqidd.mm"
include "mpt2eq123dv.mm"
include "3eqtr4rd.mm"
include "3eqtrd.mm"

theorem submatres
  let cA: class A
  let cB: class B
  let cR: class R
  let cM: class M
  let cN: class N
  let vi: setvar i
  let vj: setvar j
  assume submat1n.a: |- A = ( ( 1 ... N ) Mat R )
  assume submat1n.b: |- B = ( Base ` A )


  assert |- ( ( N e. NN /\ M e. B ) -> ( N ( subMat1 ` M ) N ) = ( M |` ( ( 1 ... ( N - 1 ) ) X. ( 1 ... ( N - 1 ) ) ) ) )

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
    cN
    cN
    cM
    csmat
    cfv
    co
    cN
    cN
    cM
    c1
    cN
    cfz
    co
    #
    cR
    csubma
    co
    #
    cfv
    co
    #
    vi
    vj
    @3
    cN
    csn
    #
    cdif
    #
    @7
    vi
    cv
    vj
    cv
    cM
    co
    #
    cmpt2
    #
    cM
    c1
    cN
    c1
    cmin
    co
    cfz
    co
    #
    @10
    cxp
    #
    cres
    #
    cA
    cB
    cR
    cM
    cN
    submat1n.a
    submat1n.b
    submat1n
    @2
    @1
    cN
    @3
    wcel
    #
    @13
    @5
    @9
    wceq
    @0
    @1
    simpr
    @0
    @13
    @1
    @0
    cN
    c1
    cuz
    cfv
    #
    wcel
    #
    @13
    @0
    @15
    cn
    @14
    cN
    nnuz
    eleq2i
    biimpi
    #
    c1
    cN
    eluzfz2
    syl
    adantr
    #
    @17
    cA
    cB
    @4
    cR
    vi
    vj
    cN
    cN
    cM
    @3
    submat1n.a
    @4
    eqid
    submat1n.b
    submaval
    syl3anc
    @2
    vi
    vj
    @3
    @3
    @8
    cmpt2
    #
    @11
    cres
    #
    vi
    vj
    @10
    @10
    @8
    cmpt2
    #
    @12
    @9
    @2
    @10
    @3
    wss
    #
    @21
    @19
    @20
    wceq
    @0
    @21
    @1
    @0
    @10
    @7
    @3
    @0
    @15
    @7
    @10
    wceq
    #
    @16
    c1
    cN
    fzdif2
    syl
    #
    @3
    @6
    difss
    syl6eqssr
    adantr
    #
    @24
    vi
    vj
    @3
    @3
    @10
    @10
    @8
    resmpt2
    syl2anc
    @1
    @12
    @19
    wceq
    @0
    @1
    cM
    @18
    @11
    cA
    cB
    cR
    vi
    vj
    cM
    @3
    submat1n.a
    submat1n.b
    matmpt2
    reseq1d
    adantl
    @2
    vi
    vj
    @7
    @7
    @8
    @10
    @10
    @8
    @0
    @22
    @1
    @23
    adantr
    #
    @25
    @2
    @8
    eqidd
    mpt2eq123dv
    3eqtr4rd
    3eqtrd
end
