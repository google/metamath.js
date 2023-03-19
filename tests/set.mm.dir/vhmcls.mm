include "crn.mm"
include "co.mm"
include "cfv.mm"
include "ssmclslem.mm"
include "unssbd.mm"
include "wfn.mm"
include "wcel.mm"
include "cmfs.mm"
include "wf.mm"
include "mvhf.mm"
include "ffn.mm"
include "3syl.mm"
include "fnfvelrn.mm"
include "syl2anc.mm"
include "sseldd.mm"

theorem vhmcls
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cT: class T
  let cE: class E
  let cH: class H
  let cK: class K
  let cV: class V
  let cX: class X
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
  let cW: class W
  let cY: class Y
  assume mclsval.d: |- D = ( mDV ` T )
  assume mclsval.e: |- E = ( mEx ` T )
  assume mclsval.c: |- C = ( mCls ` T )
  assume mclsval.1: |- ( ph -> T e. mFS )
  assume mclsval.2: |- ( ph -> K C_ D )
  assume mclsval.3: |- ( ph -> B C_ E )
  assume ssmclslem.h: |- H = ( mVH ` T )
  assume vhmcls.v: |- V = ( mVR ` T )
  assume vhmcls.3: |- ( ph -> X e. V )


  assert |- ( ph -> ( H ` X ) e. ( K C B ) )

  proof
    wph
    cH
    crn
    #
    cK
    cB
    cC
    co
    #
    cX
    cH
    cfv
    #
    wph
    cB
    @0
    @1
    wph
    cB
    cC
    cD
    cT
    cE
    cH
    cK
    mclsval.d
    mclsval.e
    mclsval.c
    mclsval.1
    mclsval.2
    mclsval.3
    ssmclslem.h
    ssmclslem
    unssbd
    wph
    cH
    cV
    wfn
    #
    cX
    cV
    wcel
    @2
    @0
    wcel
    wph
    cT
    cmfs
    wcel
    cV
    cE
    cH
    wf
    @3
    mclsval.1
    cT
    cE
    cH
    cV
    vhmcls.v
    mclsval.e
    ssmclslem.h
    mvhf
    cV
    cE
    cH
    ffn
    3syl
    vhmcls.3
    cV
    cX
    cH
    fnfvelrn
    syl2anc
    sseldd
end
