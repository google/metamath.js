include "c1o.mm"
include "cmpl.mm"
include "co.mm"
include "con0.mm"
include "eqid.mm"
include "ply1ascl.mm"
include "wcel.mm"
include "1on.mm"
include "a1i.mm"
include "cps1.mm"
include "cfv.mm"
include "ply1bas.mm"
include "subrgasclcl.mm"

theorem subrg1asclcl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let cU: class U
  let cH: class H
  let cK: class K
  let cX: class X
  assume subrg1ascl.p: |- P = ( Poly1 ` R )
  assume subrg1ascl.a: |- A = ( algSc ` P )
  assume subrg1ascl.h: |- H = ( R |`s T )
  assume subrg1ascl.u: |- U = ( Poly1 ` H )
  assume subrg1ascl.r: |- ( ph -> T e. ( SubRing ` R ) )
  assume subrg1asclcl.b: |- B = ( Base ` U )
  assume subrg1asclcl.k: |- K = ( Base ` R )
  assume subrg1asclcl.x: |- ( ph -> X e. K )


  assert |- ( ph -> ( ( A ` X ) e. B <-> X e. T ) )

  proof
    wph
    cA
    cB
    c1o
    cR
    cmpl
    co
    #
    cR
    cT
    c1o
    cH
    cmpl
    co
    #
    cH
    c1o
    cK
    con0
    cX
    @0
    eqid
    cA
    cP
    cR
    subrg1ascl.p
    subrg1ascl.a
    ply1ascl
    subrg1ascl.h
    @1
    eqid
    c1o
    con0
    wcel
    wph
    1on
    a1i
    subrg1ascl.r
    cU
    cH
    cH
    cps1
    cfv
    #
    cB
    subrg1ascl.u
    @2
    eqid
    subrg1asclcl.b
    ply1bas
    subrg1asclcl.k
    subrg1asclcl.x
    subrgasclcl
end
