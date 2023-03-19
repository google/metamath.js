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
include "oveq.mm"
include "opeq2d.mm"
include "mpt2eq3dv.mm"
include "rdgeq1.mm"
include "syl.mm"
include "imaeq1d.mm"
include "df-seq.mm"
include "3eqtr4g.mm"

theorem seqeq2
  let c.pl: class .+
  let cQ: class Q
  let cF: class F
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  let cG: class G
  let cN: class N


  assert |- ( .+ = Q -> seq M ( .+ , F ) = seq M ( Q , F ) )

  proof
    c.pl
    cQ
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
    @3
    cQ
    co
    #
    cop
    #
    cmpt2
    #
    @7
    crdg
    #
    com
    cima
    c.pl
    cF
    cM
    cseq
    cQ
    cF
    cM
    cseq
    @0
    @8
    @12
    com
    @0
    @6
    @11
    wceq
    @8
    @12
    wceq
    @0
    vx
    vy
    cvv
    cvv
    @5
    @10
    @0
    @4
    @9
    @1
    @2
    @3
    c.pl
    cQ
    oveq
    opeq2d
    mpt2eq3dv
    @7
    @6
    @11
    rdgeq1
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
    cQ
    cF
    cM
    df-seq
    3eqtr4g
end
