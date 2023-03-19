include "cr.mm"
include "crp.mm"
include "ce.mm"
include "cres.mm"
include "wf1.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wfn.mm"
include "wcel.mm"
include "cc.mm"
include "wss.mm"
include "eff.mm"
include "ffn.mm"
include "ax-mp.mm"
include "ax-resscn.mm"
include "fnssres.mm"
include "mp2an.mm"
include "fvres.mm"
include "rpefcl.mm"
include "eqeltrd.mm"
include "rgen.mm"
include "ffnfv.mm"
include "mpbir2an.mm"
include "wa.mm"
include "eqeqan12d.mm"
include "reef11.mm"
include "biimpd.mm"
include "sylbid.mm"
include "rgen2a.mm"
include "dff13.mm"

theorem reeff1
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B


  assert |- ( exp |` RR ) : RR -1-1-> RR+

  proof
    cr
    crp
    ce
    cr
    cres
    #
    wf1
    cr
    crp
    @0
    wf
    #
    vx
    cv
    #
    @0
    cfv
    #
    vy
    cv
    #
    @0
    cfv
    #
    wceq
    #
    @2
    @4
    wceq
    #
    wi
    #
    vy
    cr
    wral
    vx
    cr
    wral
    @1
    @0
    cr
    wfn
    #
    @3
    crp
    wcel
    #
    vx
    cr
    wral
    ce
    cc
    wfn
    #
    cr
    cc
    wss
    @9
    cc
    cc
    ce
    wf
    @11
    eff
    cc
    cc
    ce
    ffn
    ax-mp
    ax-resscn
    cc
    cr
    ce
    fnssres
    mp2an
    @10
    vx
    cr
    @2
    cr
    wcel
    #
    @3
    @2
    ce
    cfv
    #
    crp
    @2
    cr
    ce
    fvres
    #
    @2
    rpefcl
    eqeltrd
    rgen
    vx
    cr
    crp
    @0
    ffnfv
    mpbir2an
    @8
    vx
    vy
    cr
    @12
    @4
    cr
    wcel
    #
    wa
    #
    @6
    @13
    @4
    ce
    cfv
    #
    wceq
    #
    @7
    @12
    @15
    @3
    @13
    @5
    @17
    @14
    @4
    cr
    ce
    fvres
    eqeqan12d
    @16
    @18
    @7
    @2
    @4
    reef11
    biimpd
    sylbid
    rgen2a
    vx
    vy
    cr
    crp
    @0
    dff13
    mpbir2an
end
