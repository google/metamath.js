include "crn.mm"
include "cun.mm"
include "cv.mm"
include "wss.mm"
include "cotp.mm"
include "cmax.mm"
include "cfv.mm"
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
include "co.mm"
include "simpl.mm"
include "a1i.mm"
include "alrimiv.mm"
include "ssintab.mm"
include "sylibr.mm"
include "eqid.mm"
include "mclsval.mm"
include "sseqtr4d.mm"

theorem ssmclslem
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cT: class T
  let cE: class E
  let cH: class H
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
  assume ssmclslem.h: |- H = ( mVH ` T )


  assert |- ( ph -> ( B u. ran H ) C_ ( K C B ) )

  proof
    wph
    cB
    cH
    crn
    #
    cun
    #
    @1
    vc
    cv
    #
    wss
    #
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
    @5
    @0
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
    @4
    wbr
    @9
    cH
    cfv
    @8
    cfv
    cT
    cmvrs
    cfv
    #
    cfv
    @10
    cH
    cfv
    @8
    cfv
    @11
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
    @6
    @8
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
    #
    wa
    #
    vc
    cab
    cint
    #
    cK
    cB
    cC
    co
    wph
    @14
    @3
    wi
    #
    vc
    wal
    @1
    @15
    wss
    wph
    @16
    vc
    @16
    wph
    @3
    @13
    simpl
    a1i
    alrimiv
    @14
    vc
    @1
    ssintab
    sylibr
    wph
    vx
    vy
    @7
    cB
    cC
    cD
    @12
    cT
    vm
    vo
    cE
    cH
    cK
    @11
    vs
    vp
    vc
    mclsval.d
    mclsval.e
    mclsval.c
    mclsval.1
    mclsval.2
    mclsval.3
    ssmclslem.h
    @7
    eqid
    @12
    eqid
    @11
    eqid
    mclsval
    sseqtr4d
end
