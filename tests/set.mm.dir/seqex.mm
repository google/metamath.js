include "cseq.mm"
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
include "df-seq.mm"
include "wfun.mm"
include "wcel.mm"
include "rdgfun.mm"
include "omex.mm"
include "funimaexg.mm"
include "mp2an.mm"
include "eqeltri.mm"

theorem seqex
  let c.pl: class .+
  let cF: class F
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  let cG: class G
  let cN: class N
  let cQ: class Q


  assert |- seq M ( .+ , F ) e. _V

  proof
    c.pl
    cF
    cM
    cseq
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
    @0
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
    cop
    #
    crdg
    #
    com
    cima
    #
    cvv
    vx
    vy
    c.pl
    cF
    cM
    df-seq
    @3
    wfun
    com
    cvv
    wcel
    @4
    cvv
    wcel
    @2
    @1
    rdgfun
    omex
    @3
    com
    cvv
    funimaexg
    mp2an
    eqeltri
end
