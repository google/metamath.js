include "cjn.mm"
include "cfv.mm"
include "cmee.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "cpr.mm"
include "club.mm"
include "wbr.mm"
include "coprab.mm"
include "cglb.mm"
include "eqid.mm"
include "oduglb.mm"
include "breqd.mm"
include "oprabbidv.mm"
include "joinfval.mm"
include "codu.mm"
include "fvex.mm"
include "eqeltri.mm"
include "meetfval.mm"
include "mp1i.mm"
include "3eqtr4d.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "meet0.mm"
include "syl6eq.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem odumeet
  let cD: class D
  let c.or: class .\/
  let cO: class O
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cL: class L
  let cU: class U
  let cV: class V
  let c.an: class ./\
  assume oduglb.d: |- D = ( ODual ` O )
  assume odumeet.j: |- .\/ = ( join ` O )


  assert |- .\/ = ( meet ` D )

  proof
    c.or
    cO
    cjn
    cfv
    #
    cD
    cmee
    cfv
    #
    odumeet.j
    cO
    cvv
    wcel
    #
    @0
    @1
    wceq
    @2
    va
    cv
    vb
    cv
    cpr
    #
    vc
    cv
    #
    cO
    club
    cfv
    #
    wbr
    #
    va
    vb
    vc
    coprab
    @3
    @4
    cD
    cglb
    cfv
    #
    wbr
    #
    va
    vb
    vc
    coprab
    #
    @0
    @1
    @2
    @6
    @8
    va
    vb
    vc
    @2
    @5
    @7
    @3
    @4
    cD
    @5
    cO
    cvv
    oduglb.d
    @5
    eqid
    #
    oduglb
    breqd
    oprabbidv
    va
    vb
    vc
    @5
    @0
    cO
    cvv
    @10
    @0
    eqid
    joinfval
    cD
    cvv
    wcel
    @1
    @9
    wceq
    @2
    cD
    cO
    codu
    cfv
    #
    cvv
    oduglb.d
    cO
    codu
    fvex
    eqeltri
    va
    vb
    vc
    @7
    cD
    @1
    cvv
    @7
    eqid
    @1
    eqid
    meetfval
    mp1i
    3eqtr4d
    @2
    wn
    #
    @0
    c0
    @1
    cO
    cjn
    fvprc
    @12
    @1
    c0
    cmee
    cfv
    c0
    @12
    cD
    c0
    cmee
    @12
    cD
    @11
    c0
    oduglb.d
    cO
    codu
    fvprc
    syl5eq
    fveq2d
    meet0
    syl6eq
    eqtr4d
    pm2.61i
    eqtri
end
