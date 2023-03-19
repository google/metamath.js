include "cbs.mm"
include "cfv.mm"
include "cxpc.mm"
include "co.mm"
include "chomf.mm"
include "crn.mm"
include "cun.mm"
include "csetc.mm"
include "cfuc.mm"
include "ccid.mm"
include "cevlf.mm"
include "chof.mm"
include "cinv.mm"
include "cfunc.mm"
include "cv.mm"
include "c1st.mm"
include "cnat.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "chom.mm"
include "c2nd.mm"
include "cvv.mm"
include "ctpos.mm"
include "cop.mm"
include "c2ndf.mm"
include "ccofu.mm"
include "c1stf.mm"
include "cprf.mm"
include "eqid.mm"
include "wcel.mm"
include "fvex.mm"
include "rnex.mm"
include "unexg.mm"
include "sylancr.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "yonffthlem.mm"

theorem yonffth
  let wph: wff ph
  let cC: class C
  let cQ: class Q
  let cS: class S
  let cU: class U
  let cO: class O
  let cV: class V
  let cY: class Y
  let va: setvar a
  let vf: setvar f
  let vg: setvar g
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  assume yonffth.y: |- Y = ( Yon ` C )
  assume yonffth.o: |- O = ( oppCat ` C )
  assume yonffth.s: |- S = ( SetCat ` U )
  assume yonffth.q: |- Q = ( O FuncCat S )
  assume yonffth.c: |- ( ph -> C e. Cat )
  assume yonffth.u: |- ( ph -> U e. V )
  assume yonffth.h: |- ( ph -> ran ( Homf ` C ) C_ U )


  assert |- ( ph -> Y e. ( ( C Full Q ) i^i ( C Faith Q ) ) )

  proof
    wph
    vx
    vy
    vu
    cC
    cbs
    cfv
    #
    cC
    cQ
    cQ
    cO
    cxpc
    co
    cQ
    chomf
    cfv
    #
    crn
    #
    cU
    cun
    #
    csetc
    cfv
    #
    cfuc
    co
    #
    cS
    @4
    cU
    cC
    ccid
    cfv
    #
    vf
    vg
    cO
    cS
    cevlf
    co
    #
    cQ
    chof
    cfv
    #
    @5
    cinv
    cfv
    #
    vf
    vx
    cO
    cS
    cfunc
    co
    #
    @0
    va
    vx
    cv
    #
    cY
    c1st
    cfv
    #
    cfv
    vf
    cv
    #
    cO
    cS
    cnat
    co
    co
    @11
    @6
    cfv
    @11
    va
    cv
    cfv
    cfv
    cmpt
    cmpt2
    #
    vf
    vx
    @10
    @0
    vu
    @11
    @13
    c1st
    cfv
    cfv
    vy
    @0
    vg
    vy
    cv
    #
    @11
    cC
    chom
    cfv
    co
    vu
    cv
    vg
    cv
    @11
    @15
    @13
    c2nd
    cfv
    co
    cfv
    cfv
    cmpt
    cmpt
    cmpt
    cmpt2
    #
    cO
    @3
    cvv
    cY
    @8
    @12
    cY
    c2nd
    cfv
    ctpos
    cop
    cQ
    cO
    c2ndf
    co
    ccofu
    co
    cQ
    cO
    c1stf
    co
    cprf
    co
    ccofu
    co
    #
    va
    yonffth.y
    @0
    eqid
    @6
    eqid
    yonffth.o
    yonffth.s
    @4
    eqid
    yonffth.q
    @8
    eqid
    @5
    eqid
    @7
    eqid
    @17
    eqid
    yonffth.c
    wph
    @2
    cvv
    wcel
    cU
    cV
    wcel
    @3
    cvv
    wcel
    @1
    cQ
    chomf
    fvex
    rnex
    yonffth.u
    @2
    cU
    cvv
    cV
    unexg
    sylancr
    yonffth.h
    @3
    @3
    wss
    wph
    @3
    ssid
    a1i
    @14
    eqid
    @9
    eqid
    @16
    eqid
    yonffthlem
end
