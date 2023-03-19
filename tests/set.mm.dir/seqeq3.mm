include "wceq.mm"
include "cvv.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfv.mm"
include "cop.mm"
include "cmpt2.mm"
include "crdg.mm"
include "com.mm"
include "cima.mm"
include "cseq.mm"
include "fveq1.mm"
include "oveq2d.mm"
include "opeq2d.mm"
include "mpt2eq3dv.mm"
include "rdgeq12.mm"
include "syl2anc.mm"
include "imaeq1d.mm"
include "df-seq.mm"
include "3eqtr4g.mm"

theorem seqeq3
  let c.pl: class .+
  let cF: class F
  let cG: class G
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  let cN: class N
  let cQ: class Q


  assert |- ( F = G -> seq M ( .+ , F ) = seq M ( .+ , G ) )

  proof
    cF
    cG
    wceq
    #
    vx
    vy
    cvv
    cvv
    vx
    cv
    c1
    caddc
    co
    #
    vy
    cv
    #
    @1
    cF
    cfv
    #
    c.pl
    co
    #
    cop
    #
    cmpt2
    #
    cM
    cM
    cF
    cfv
    #
    cop
    #
    crdg
    #
    com
    cima
    vx
    vy
    cvv
    cvv
    @1
    @2
    @1
    cG
    cfv
    #
    c.pl
    co
    #
    cop
    #
    cmpt2
    #
    cM
    cM
    cG
    cfv
    #
    cop
    #
    crdg
    #
    com
    cima
    c.pl
    cF
    cM
    cseq
    c.pl
    cG
    cM
    cseq
    @0
    @9
    @16
    com
    @0
    @6
    @13
    wceq
    @8
    @15
    wceq
    @9
    @16
    wceq
    @0
    vx
    vy
    cvv
    cvv
    @5
    @12
    @0
    @4
    @11
    @1
    @0
    @3
    @10
    @2
    c.pl
    @1
    cF
    cG
    fveq1
    oveq2d
    opeq2d
    mpt2eq3dv
    @0
    @7
    @14
    cM
    cM
    cF
    cG
    fveq1
    opeq2d
    @8
    @15
    @6
    @13
    rdgeq12
    syl2anc
    imaeq1d
    vx
    vy
    c.pl
    cF
    cM
    df-seq
    vx
    vy
    c.pl
    cG
    cM
    df-seq
    3eqtr4g
end
