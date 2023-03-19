include "c0.mm"
include "c1o.mm"
include "cmvr.mm"
include "co.mm"
include "cfv.mm"
include "vr1val.mm"
include "wf.mm"
include "wcel.mm"
include "cmpl.mm"
include "con0.mm"
include "eqid.mm"
include "1on.mm"
include "a1i.mm"
include "cps1.mm"
include "ply1bas.mm"
include "subrgmvrf.mm"
include "0lt1o.mm"
include "ffvelrn.mm"
include "sylancl.mm"
include "syl5eqel.mm"

theorem subrgvr1cl
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cT: class T
  let cU: class U
  let cH: class H
  let cX: class X
  assume subrgvr1.x: |- X = ( var1 ` R )
  assume subrgvr1.r: |- ( ph -> T e. ( SubRing ` R ) )
  assume subrgvr1.h: |- H = ( R |`s T )
  assume subrgvr1cl.u: |- U = ( Poly1 ` H )
  assume subrgvr1cl.b: |- B = ( Base ` U )


  assert |- ( ph -> X e. B )

  proof
    wph
    cX
    c0
    c1o
    cR
    cmvr
    co
    #
    cfv
    #
    cB
    cR
    cX
    subrgvr1.x
    vr1val
    wph
    c1o
    cB
    @0
    wf
    c0
    c1o
    wcel
    @1
    cB
    wcel
    wph
    cB
    cR
    cT
    c1o
    cH
    cmpl
    co
    #
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
    @2
    eqid
    cU
    cH
    cH
    cps1
    cfv
    #
    cB
    subrgvr1cl.u
    @3
    eqid
    subrgvr1cl.b
    ply1bas
    subrgmvrf
    0lt1o
    c1o
    cB
    c0
    @0
    ffvelrn
    sylancl
    syl5eqel
end
