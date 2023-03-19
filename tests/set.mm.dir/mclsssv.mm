include "co.mm"
include "cmvh.mm"
include "cfv.mm"
include "crn.mm"
include "cun.mm"
include "cv.mm"
include "wss.mm"
include "cotp.mm"
include "cmax.mm"
include "wcel.mm"
include "cima.mm"
include "wbr.mm"
include "cmvrs.mm"
include "cxp.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "cmsub.mm"
include "wral.mm"
include "cab.mm"
include "cint.mm"
include "eqid.mm"
include "mclsval.mm"
include "mclsssvlem.mm"
include "eqsstrd.mm"

theorem mclsssv
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cT: class T
  let cE: class E
  let cK: class K
  let vd: setvar d
  let vh: setvar h
  let vt: setvar t
  let vc: setvar c
  let vm: setvar m
  let vo: setvar o
  let vp: setvar p
  let vs: setvar s
  let vv: setvar v
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vz: setvar z
  let cH: class H
  let vy: setvar y
  let cL: class L
  let cA: class A
  let cO: class O
  let cS: class S
  let cM: class M
  let cP: class P
  let cQ: class Q
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume mclsval.d: |- D = ( mDV ` T )
  assume mclsval.e: |- E = ( mEx ` T )
  assume mclsval.c: |- C = ( mCls ` T )
  assume mclsval.1: |- ( ph -> T e. mFS )
  assume mclsval.2: |- ( ph -> K C_ D )
  assume mclsval.3: |- ( ph -> B C_ E )


  assert |- ( ph -> ( K C B ) C_ E )

  proof
    wph
    cK
    cB
    cC
    co
    cB
    cT
    cmvh
    cfv
    #
    crn
    #
    cun
    vc
    cv
    #
    wss
    vm
    cv
    #
    vo
    cv
    #
    vp
    cv
    #
    cotp
    cT
    cmax
    cfv
    #
    wcel
    vs
    cv
    #
    @4
    @1
    cun
    cima
    @2
    wss
    vx
    cv
    #
    vy
    cv
    #
    @3
    wbr
    @8
    @0
    cfv
    @7
    cfv
    cT
    cmvrs
    cfv
    #
    cfv
    @9
    @0
    cfv
    @7
    cfv
    @10
    cfv
    cxp
    cK
    wss
    wi
    vy
    wal
    vx
    wal
    wa
    @5
    @7
    cfv
    @2
    wcel
    wi
    vs
    cT
    cmsub
    cfv
    #
    crn
    wral
    wi
    vp
    wal
    vo
    wal
    vm
    wal
    wa
    vc
    cab
    cint
    cE
    wph
    vx
    vy
    @6
    cB
    cC
    cD
    @11
    cT
    vm
    vo
    cE
    @0
    cK
    @10
    vs
    vp
    vc
    mclsval.d
    mclsval.e
    mclsval.c
    mclsval.1
    mclsval.2
    mclsval.3
    @0
    eqid
    #
    @6
    eqid
    #
    @11
    eqid
    #
    @10
    eqid
    #
    mclsval
    wph
    vx
    vy
    @6
    cB
    cC
    cD
    @11
    cT
    vm
    vo
    cE
    @0
    cK
    @10
    vs
    vp
    vc
    mclsval.d
    mclsval.e
    mclsval.c
    mclsval.1
    mclsval.2
    mclsval.3
    @12
    @13
    @14
    @15
    mclsssvlem
    eqsstrd
end
