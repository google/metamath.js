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
include "fveq2.mm"
include "opeq12.mm"
include "mpdan.mm"
include "rdgeq2.mm"
include "syl.mm"
include "imaeq1d.mm"
include "df-seq.mm"
include "3eqtr4g.mm"

theorem seqeq1
  let c.pl: class .+
  let cF: class F
  let cM: class M
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let cG: class G
  let cQ: class Q


  assert |- ( M = N -> seq M ( .+ , F ) = seq N ( .+ , F ) )

  proof
    cM
    cN
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
    @1
    cF
    cfv
    c.pl
    co
    cop
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
    @2
    cN
    cN
    cF
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
    cF
    cN
    cseq
    @0
    @5
    @8
    com
    @0
    @4
    @7
    wceq
    #
    @5
    @8
    wceq
    @0
    @3
    @6
    wceq
    @9
    cM
    cN
    cF
    fveq2
    cM
    @3
    cN
    @6
    opeq12
    mpdan
    @4
    @7
    @2
    rdgeq2
    syl
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
    cF
    cN
    df-seq
    3eqtr4g
end
