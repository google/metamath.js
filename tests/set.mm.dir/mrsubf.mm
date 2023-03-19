include "crn.mm"
include "wcel.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "cvv.mm"
include "cmvar.mm"
include "cfv.mm"
include "cpm.mm"
include "wss.mm"
include "c0.mm"
include "wceq.mm"
include "n0i.mm"
include "wn.mm"
include "cmrsub.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "rneqd.mm"
include "rn0.mm"
include "syl6eq.mm"
include "nsyl2.mm"
include "eqid.mm"
include "mrsubff.mm"
include "frn.mm"
include "3syl.mm"
include "id.mm"
include "sseldd.mm"
include "elmapi.mm"
include "syl.mm"

theorem mrsubf
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  let vc: setvar c
  let vf: setvar f
  let vr: setvar r
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let vw: setvar w
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume mrsubccat.s: |- S = ( mRSubst ` T )
  assume mrsubccat.r: |- R = ( mREx ` T )


  assert |- ( F e. ran S -> F : R --> R )

  proof
    cF
    cS
    crn
    #
    wcel
    #
    cF
    cR
    cR
    cmap
    co
    #
    wcel
    cR
    cR
    cF
    wf
    @1
    @0
    @2
    cF
    @1
    cT
    cvv
    wcel
    #
    cR
    cT
    cmvar
    cfv
    #
    cpm
    co
    #
    @2
    cS
    wf
    @0
    @2
    wss
    @1
    @0
    c0
    wceq
    @3
    @0
    cF
    n0i
    @3
    wn
    #
    @0
    c0
    crn
    c0
    @6
    cS
    c0
    @6
    cS
    cT
    cmrsub
    cfv
    c0
    mrsubccat.s
    cT
    cmrsub
    fvprc
    syl5eq
    rneqd
    rn0
    syl6eq
    nsyl2
    cR
    cS
    cT
    @4
    cvv
    @4
    eqid
    mrsubccat.r
    mrsubccat.s
    mrsubff
    @5
    @2
    cS
    frn
    3syl
    @1
    id
    sseldd
    cF
    cR
    cR
    elmapi
    syl
end
