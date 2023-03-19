include "chil.mm"
include "ch0o.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "cado.mm"
include "ho0f.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "c0v.mm"
include "ho0val.mm"
include "oveq1d.mm"
include "hi01.mm"
include "sylan9eq.mm"
include "oveq2d.mm"
include "hi02.mm"
include "sylan9eqr.mm"
include "eqtr4d.mm"
include "rgen2a.mm"
include "adjeq.mm"
include "mp3an.mm"

theorem adj0
  let vx: setvar x
  let vy: setvar y


  assert |- ( adjh ` 0hop ) = 0hop

  proof
    chil
    chil
    ch0o
    wf
    #
    @0
    vx
    cv
    #
    ch0o
    cfv
    #
    vy
    cv
    #
    csp
    co
    #
    @1
    @3
    ch0o
    cfv
    #
    csp
    co
    #
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    ch0o
    cado
    cfv
    ch0o
    wceq
    ho0f
    ho0f
    @7
    vx
    vy
    chil
    @1
    chil
    wcel
    #
    @3
    chil
    wcel
    #
    wa
    @4
    cc0
    @6
    @8
    @9
    @4
    c0v
    @3
    csp
    co
    cc0
    @8
    @2
    c0v
    @3
    csp
    @1
    ho0val
    oveq1d
    @3
    hi01
    sylan9eq
    @9
    @8
    @6
    @1
    c0v
    csp
    co
    cc0
    @9
    @5
    c0v
    @1
    csp
    @3
    ho0val
    oveq2d
    @1
    hi02
    sylan9eqr
    eqtr4d
    rgen2a
    vx
    vy
    ch0o
    ch0o
    adjeq
    mp3an
end
