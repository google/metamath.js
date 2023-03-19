include "cn0.mm"
include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "cmg.mm"
include "co.mm"
include "c0g.mm"
include "wceq.mm"
include "cn.mm"
include "crab.mm"
include "c0.mm"
include "cc0.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cif.mm"
include "csb.mm"
include "c0ex.mm"
include "ltso.mm"
include "infex.mm"
include "ifex.mm"
include "csbex.mm"
include "eqid.mm"
include "odfval.mm"
include "fnmpti.mm"
include "odcl.mm"
include "rgen.mm"
include "ffnfv.mm"
include "mpbir2an.mm"

theorem odf
  let cG: class G
  let cO: class O
  let cX: class X
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let c.0: class .0.
  let vx: setvar x
  let cA: class A
  let cN: class N
  let c.x: class .x.
  assume odcl.1: |- X = ( Base ` G )
  assume odcl.2: |- O = ( od ` G )


  assert |- O : X --> NN0

  proof
    cX
    cn0
    cO
    wf
    cO
    cX
    wfn
    vx
    cv
    #
    cO
    cfv
    cn0
    wcel
    #
    vx
    cX
    wral
    vy
    cX
    vw
    vz
    cv
    vy
    cv
    cG
    cmg
    cfv
    #
    co
    cG
    c0g
    cfv
    #
    wceq
    vz
    cn
    crab
    #
    vw
    cv
    #
    c0
    wceq
    #
    cc0
    @5
    cr
    clt
    cinf
    #
    cif
    #
    csb
    cO
    vw
    @4
    @8
    @6
    cc0
    @7
    c0ex
    cr
    @5
    clt
    ltso
    infex
    ifex
    csbex
    vy
    vz
    @2
    vw
    cG
    cO
    cX
    @3
    odcl.1
    @2
    eqid
    @3
    eqid
    odcl.2
    odfval
    fnmpti
    @1
    vx
    cX
    @0
    cG
    cO
    cX
    odcl.1
    odcl.2
    odcl
    rgen
    vx
    cX
    cn0
    cO
    ffnfv
    mpbir2an
end
