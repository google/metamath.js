include "cmvh.mm"
include "cfv.mm"
include "crn.mm"
include "co.mm"
include "eqid.mm"
include "ssmclslem.mm"
include "unssad.mm"

theorem ssmcls
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


  assert |- ( ph -> B C_ ( K C B ) )

  proof
    wph
    cB
    cT
    cmvh
    cfv
    #
    crn
    cK
    cB
    cC
    co
    wph
    cB
    cC
    cD
    cT
    cE
    @0
    cK
    mclsval.d
    mclsval.e
    mclsval.c
    mclsval.1
    mclsval.2
    mclsval.3
    @0
    eqid
    ssmclslem
    unssad
end
