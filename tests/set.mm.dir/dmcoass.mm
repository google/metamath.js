include "cdm.mm"
include "cv.mm"
include "csn.mm"
include "ccoda.mm"
include "cfv.mm"
include "cdoma.mm"
include "wceq.mm"
include "crab.mm"
include "cxp.mm"
include "ciun.mm"
include "c2nd.mm"
include "cop.mm"
include "cco.mm"
include "co.mm"
include "cotp.mm"
include "eqid.mm"
include "coafval.mm"
include "dmmpt2ssx.mm"
include "wss.mm"
include "iunss.mm"
include "wcel.mm"
include "snssi.mm"
include "ssrab2.mm"
include "xpss12.mm"
include "sylancl.mm"
include "mprgbir.mm"
include "sstri.mm"

theorem dmcoass
  let cA: class A
  let cC: class C
  let c.x: class .x.
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cF: class F
  let cG: class G
  let c.xb: class .xb
  assume coafval.o: |- .x. = ( compA ` C )
  assume coafval.a: |- A = ( Arrow ` C )


  assert |- dom .x. C_ ( A X. A )

  proof
    c.x
    cdm
    vg
    cA
    vg
    cv
    #
    csn
    #
    vh
    cv
    ccoda
    cfv
    @0
    cdoma
    cfv
    #
    wceq
    #
    vh
    cA
    crab
    #
    cxp
    #
    ciun
    #
    cA
    cA
    cxp
    #
    vg
    vf
    cA
    @4
    vf
    cv
    #
    cdoma
    cfv
    #
    @0
    ccoda
    cfv
    #
    @0
    c2nd
    cfv
    @8
    c2nd
    cfv
    @9
    @2
    cop
    @10
    cC
    cco
    cfv
    #
    co
    co
    cotp
    c.x
    cA
    cC
    @11
    c.x
    vf
    vg
    vh
    coafval.o
    coafval.a
    @11
    eqid
    coafval
    dmmpt2ssx
    @6
    @7
    wss
    @5
    @7
    wss
    #
    vg
    cA
    vg
    cA
    @5
    @7
    iunss
    @0
    cA
    wcel
    @1
    cA
    wss
    @4
    cA
    wss
    @12
    @0
    cA
    snssi
    @3
    vh
    cA
    ssrab2
    @1
    cA
    @4
    cA
    xpss12
    sylancl
    mprgbir
    sstri
end
