include "co.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "ccat.mm"
include "n0i.mm"
include "wn.mm"
include "choma.mm"
include "cfv.mm"
include "cv.mm"
include "cbs.mm"
include "cxp.mm"
include "csn.mm"
include "chom.mm"
include "cmpt.mm"
include "df-homa.mm"
include "fvmptndm.mm"
include "syl5eq.mm"
include "oveqd.mm"
include "0ov.mm"
include "syl6eq.mm"
include "nsyl2.mm"

theorem homarcl
  let cC: class C
  let cF: class F
  let cH: class H
  let cX: class X
  let cY: class Y
  let vc: setvar c
  let vx: setvar x
  let vz: setvar z
  let cB: class B
  let cJ: class J
  let wph: wff ph
  assume homarcl.h: |- H = ( HomA ` C )


  assert |- ( F e. ( X H Y ) -> C e. Cat )

  proof
    cF
    cX
    cY
    cH
    co
    #
    wcel
    @0
    c0
    wceq
    cC
    ccat
    wcel
    #
    @0
    cF
    n0i
    @1
    wn
    #
    @0
    cX
    cY
    c0
    co
    c0
    @2
    cH
    c0
    cX
    cY
    @2
    cH
    cC
    choma
    cfv
    c0
    homarcl.h
    vc
    ccat
    vx
    vc
    cv
    #
    cbs
    cfv
    #
    @4
    cxp
    vx
    cv
    #
    csn
    @5
    @3
    chom
    cfv
    cfv
    cxp
    cmpt
    choma
    cC
    vx
    vc
    df-homa
    fvmptndm
    syl5eq
    oveqd
    cX
    cY
    0ov
    syl6eq
    nsyl2
end
