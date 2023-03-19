include "ccat.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "ccic.mm"
include "wrel.mm"
include "ciso.mm"
include "c0.mm"
include "csupp.mm"
include "co.mm"
include "cv.mm"
include "wne.mm"
include "cxp.mm"
include "crab.mm"
include "cop.mm"
include "w3a.mm"
include "copab.mm"
include "relopab.mm"
include "a1i.mm"
include "wceq.mm"
include "fveq2.mm"
include "neeq1d.mm"
include "rabxp.mm"
include "releqd.mm"
include "mpbird.mm"
include "wfn.mm"
include "cvv.mm"
include "isofn.mm"
include "fvex.mm"
include "sqxpexg.mm"
include "mp1i.mm"
include "0ex.mm"
include "suppvalfn.mm"
include "syl3anc.mm"
include "cicfval.mm"
include "cicsym.mm"
include "wbr.mm"
include "cictr.mm"
include "3expb.mm"
include "cicref.mm"
include "ciclcl.mm"
include "impbida.mm"
include "iserd.mm"

theorem cicer
  let cC: class C
  let vf: setvar f
  let vg: setvar g
  let cR: class R
  let cS: class S
  let cT: class T
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( C e. Cat -> ( ~=c ` C ) Er ( Base ` C ) )

  proof
    cC
    ccat
    wcel
    #
    vx
    vy
    vz
    cC
    cbs
    cfv
    #
    cC
    ccic
    cfv
    #
    @0
    @2
    wrel
    cC
    ciso
    cfv
    #
    c0
    csupp
    co
    #
    wrel
    #
    @0
    @5
    vf
    cv
    #
    @3
    cfv
    #
    c0
    wne
    #
    vf
    @1
    @1
    cxp
    #
    crab
    #
    wrel
    #
    @0
    @11
    vx
    cv
    #
    @1
    wcel
    #
    vy
    cv
    #
    @1
    wcel
    @12
    @14
    cop
    #
    @3
    cfv
    #
    c0
    wne
    #
    w3a
    #
    vx
    vy
    copab
    #
    wrel
    #
    @20
    @0
    @18
    vx
    vy
    relopab
    a1i
    @0
    @10
    @19
    @10
    @19
    wceq
    @0
    @8
    @17
    vf
    vx
    vy
    @1
    @1
    @6
    @15
    wceq
    @7
    @16
    c0
    @6
    @15
    @3
    fveq2
    neeq1d
    rabxp
    a1i
    releqd
    mpbird
    @0
    @4
    @10
    @0
    @3
    @9
    wfn
    @9
    cvv
    wcel
    #
    c0
    cvv
    wcel
    #
    @4
    @10
    wceq
    cC
    isofn
    @1
    cvv
    wcel
    @21
    @0
    cC
    cbs
    fvex
    @1
    cvv
    sqxpexg
    mp1i
    @22
    @0
    0ex
    a1i
    vf
    @3
    cvv
    cvv
    @9
    c0
    suppvalfn
    syl3anc
    releqd
    mpbird
    @0
    @2
    @4
    cC
    cicfval
    releqd
    mpbird
    cC
    @12
    @14
    cicsym
    @0
    @12
    @14
    @2
    wbr
    @14
    vz
    cv
    #
    @2
    wbr
    @12
    @23
    @2
    wbr
    cC
    @12
    @14
    @23
    cictr
    3expb
    @0
    @13
    @12
    @12
    @2
    wbr
    cC
    @12
    cicref
    cC
    @12
    @12
    ciclcl
    impbida
    iserd
end
