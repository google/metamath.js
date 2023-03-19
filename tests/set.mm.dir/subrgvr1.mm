include "c0.mm"
include "c1o.mm"
include "cmvr.mm"
include "co.mm"
include "cfv.mm"
include "cv1.mm"
include "con0.mm"
include "eqid.mm"
include "wcel.mm"
include "1on.mm"
include "a1i.mm"
include "subrgmvr.mm"
include "fveq1d.mm"
include "vr1val.mm"
include "3eqtr4g.mm"

theorem subrgvr1
  let wph: wff ph
  let cR: class R
  let cT: class T
  let cH: class H
  let cX: class X
  assume subrgvr1.x: |- X = ( var1 ` R )
  assume subrgvr1.r: |- ( ph -> T e. ( SubRing ` R ) )
  assume subrgvr1.h: |- H = ( R |`s T )


  assert |- ( ph -> X = ( var1 ` H ) )

  proof
    wph
    c0
    c1o
    cR
    cmvr
    co
    #
    cfv
    c0
    c1o
    cH
    cmvr
    co
    #
    cfv
    cX
    cH
    cv1
    cfv
    #
    wph
    c0
    @0
    @1
    wph
    cR
    cT
    cH
    c1o
    @0
    con0
    @0
    eqid
    c1o
    con0
    wcel
    wph
    1on
    a1i
    subrgvr1.r
    subrgvr1.h
    subrgmvr
    fveq1d
    cR
    cX
    subrgvr1.x
    vr1val
    cH
    @2
    @2
    eqid
    vr1val
    3eqtr4g
end
