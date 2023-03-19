include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "wf.mm"
include "caddc.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "w3a.mm"
include "cfv.mm"
include "cres.mm"
include "cn0.mm"
include "wb.mm"
include "nnm1nn0.mm"
include "eqid.mm"
include "fseq1p1m1.mm"
include "syl.mm"
include "cc.mm"
include "nncn.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "opeq1d.mm"
include "sneqd.mm"
include "syl6eqr.mm"
include "uneq2d.mm"
include "eqeq2d.mm"
include "3anbi3d.mm"
include "oveq2d.mm"
include "feq2d.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "3anbi12d.mm"
include "3bitr3d.mm"

theorem fseq1m1p1
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cH: class H
  let cN: class N
  assume fseq1m1p1.1: |- H = { <. N , B >. }


  assert |- ( N e. NN -> ( ( F : ( 1 ... ( N - 1 ) ) --> A /\ B e. A /\ G = ( F u. H ) ) <-> ( G : ( 1 ... N ) --> A /\ ( G ` N ) = B /\ F = ( G |` ( 1 ... ( N - 1 ) ) ) ) ) )

  proof
    cN
    cn
    wcel
    #
    c1
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    cA
    cF
    wf
    #
    cB
    cA
    wcel
    #
    cG
    cF
    @1
    c1
    caddc
    co
    #
    cB
    cop
    #
    csn
    #
    cun
    #
    wceq
    #
    w3a
    #
    c1
    @5
    cfz
    co
    #
    cA
    cG
    wf
    #
    @5
    cG
    cfv
    #
    cB
    wceq
    #
    cF
    cG
    @2
    cres
    wceq
    #
    w3a
    #
    @3
    @4
    cG
    cF
    cH
    cun
    #
    wceq
    #
    w3a
    c1
    cN
    cfz
    co
    #
    cA
    cG
    wf
    #
    cN
    cG
    cfv
    #
    cB
    wceq
    #
    @15
    w3a
    @0
    @1
    cn0
    wcel
    @10
    @16
    wb
    cN
    nnm1nn0
    cA
    cB
    cF
    cG
    @7
    @1
    @7
    eqid
    fseq1p1m1
    syl
    @0
    @9
    @18
    @3
    @4
    @0
    @8
    @17
    cG
    @0
    @7
    cH
    cF
    @0
    @7
    cN
    cB
    cop
    #
    csn
    cH
    @0
    @6
    @23
    @0
    @5
    cN
    cB
    @0
    cN
    cc
    wcel
    c1
    cc
    wcel
    @5
    cN
    wceq
    cN
    nncn
    ax-1cn
    cN
    c1
    npcan
    sylancl
    #
    opeq1d
    sneqd
    fseq1m1p1.1
    syl6eqr
    uneq2d
    eqeq2d
    3anbi3d
    @0
    @12
    @20
    @14
    @22
    @15
    @0
    @11
    @19
    cA
    cG
    @0
    @5
    cN
    c1
    cfz
    @24
    oveq2d
    feq2d
    @0
    @13
    @21
    cB
    @0
    @5
    cN
    cG
    @24
    fveq2d
    eqeq1d
    3anbi12d
    3bitr3d
end
