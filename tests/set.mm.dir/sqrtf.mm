include "cc.mm"
include "csqrt.mm"
include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "cre.mm"
include "cle.mm"
include "wbr.mm"
include "ci.mm"
include "cmul.mm"
include "crp.mm"
include "wnel.mm"
include "w3a.mm"
include "crio.mm"
include "riotaex.mm"
include "df-sqrt.mm"
include "fnmpti.mm"
include "sqrtcl.mm"
include "rgen.mm"
include "ffnfv.mm"
include "mpbir2an.mm"

theorem sqrtf
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- sqrt : CC --> CC

  proof
    cc
    cc
    csqrt
    wf
    csqrt
    cc
    wfn
    vx
    cv
    #
    csqrt
    cfv
    cc
    wcel
    #
    vx
    cc
    wral
    vx
    cc
    vy
    cv
    #
    c2
    cexp
    co
    @0
    wceq
    cc0
    @2
    cre
    cfv
    cle
    wbr
    ci
    @2
    cmul
    co
    crp
    wnel
    w3a
    #
    vy
    cc
    crio
    csqrt
    @3
    vy
    cc
    riotaex
    vx
    vy
    df-sqrt
    fnmpti
    @1
    vx
    cc
    @0
    sqrtcl
    rgen
    vx
    cc
    cc
    csqrt
    ffnfv
    mpbir2an
end
