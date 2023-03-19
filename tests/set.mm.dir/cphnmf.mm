include "ccph.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "csqrt.mm"
include "cfv.mm"
include "cmpt.mm"
include "wa.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "simpl.mm"
include "cphl.mm"
include "cphphl.mm"
include "adantr.mm"
include "simpr.mm"
include "ipcl.mm"
include "syl3anc.mm"
include "c2.mm"
include "cexp.mm"
include "nmsq.mm"
include "cngp.mm"
include "cphngp.mm"
include "nmcl.mm"
include "sylan.mm"
include "resqcld.mm"
include "eqeltrrd.mm"
include "sqge0d.mm"
include "breqtrd.mm"
include "cphsqrtcl.mm"
include "syl13anc.mm"
include "eqid.mm"
include "fmptd.mm"
include "cphnmfval.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem cphnmf
  let cF: class F
  let c.xi: class .,
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cA: class A
  let vx: setvar x
  assume nmsq.v: |- V = ( Base ` W )
  assume nmsq.h: |- ., = ( .i ` W )
  assume nmsq.n: |- N = ( norm ` W )
  assume cphnmcl.f: |- F = ( Scalar ` W )
  assume cphnmcl.k: |- K = ( Base ` F )


  assert |- ( W e. CPreHil -> N : V --> K )

  proof
    cW
    ccph
    wcel
    #
    cV
    cK
    cN
    wf
    cV
    cK
    vx
    cV
    vx
    cv
    #
    @1
    c.xi
    co
    #
    csqrt
    cfv
    #
    cmpt
    #
    wf
    @0
    vx
    cV
    @3
    cK
    @4
    @0
    @1
    cV
    wcel
    #
    wa
    #
    @0
    @2
    cK
    wcel
    #
    @2
    cr
    wcel
    cc0
    @2
    cle
    wbr
    @3
    cK
    wcel
    @0
    @5
    simpl
    @6
    cW
    cphl
    wcel
    #
    @5
    @5
    @7
    @0
    @8
    @5
    cW
    cphphl
    adantr
    @0
    @5
    simpr
    #
    @9
    @1
    @1
    cF
    c.xi
    cK
    cV
    cW
    cphnmcl.f
    nmsq.h
    nmsq.v
    cphnmcl.k
    ipcl
    syl3anc
    @6
    @1
    cN
    cfv
    #
    c2
    cexp
    co
    #
    @2
    cr
    @1
    c.xi
    cN
    cV
    cW
    nmsq.v
    nmsq.h
    nmsq.n
    nmsq
    #
    @6
    @10
    @0
    cW
    cngp
    wcel
    @5
    @10
    cr
    wcel
    cW
    cphngp
    @1
    cW
    cN
    cV
    nmsq.v
    nmsq.n
    nmcl
    sylan
    #
    resqcld
    eqeltrrd
    @6
    cc0
    @11
    @2
    cle
    @6
    @10
    @13
    sqge0d
    @12
    breqtrd
    @2
    cF
    cK
    cW
    cphnmcl.f
    cphnmcl.k
    cphsqrtcl
    syl13anc
    @4
    eqid
    fmptd
    @0
    cV
    cK
    cN
    @4
    vx
    c.xi
    cN
    cV
    cW
    nmsq.v
    nmsq.h
    nmsq.n
    cphnmfval
    feq1d
    mpbird
end
