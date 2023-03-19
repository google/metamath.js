include "cmgp.mm"
include "cfv.mm"
include "eqid.mm"
include "mgptopn.mm"
include "mgpplusg.mm"
include "ctrg.mm"
include "wcel.mm"
include "ctmd.mm"
include "trgtmd.mm"
include "syl.mm"
include "cnmpt2plusg.mm"

theorem cnmpt2mulr
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cJ: class J
  let cK: class K
  let cL: class L
  let cX: class X
  let cY: class Y
  assume mulrcn.j: |- J = ( TopOpen ` R )
  assume cnmpt1mulr.t: |- .x. = ( .r ` R )
  assume cnmpt1mulr.r: |- ( ph -> R e. TopRing )
  assume cnmpt1mulr.k: |- ( ph -> K e. ( TopOn ` X ) )
  assume cnmpt2mulr.l: |- ( ph -> L e. ( TopOn ` Y ) )
  assume cnmpt2mulr.a: |- ( ph -> ( x e. X , y e. Y |-> A ) e. ( ( K tX L ) Cn J ) )
  assume cnmpt2mulr.b: |- ( ph -> ( x e. X , y e. Y |-> B ) e. ( ( K tX L ) Cn J ) )

  disjoint x y
  disjoint J x
  disjoint J y
  disjoint K x
  disjoint ph x
  disjoint ph y
  disjoint R x
  disjoint R y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( ph -> ( x e. X , y e. Y |-> ( A .x. B ) ) e. ( ( K tX L ) Cn J ) )

  proof
    wph
    vx
    vy
    cA
    cB
    c.x
    cR
    cmgp
    cfv
    #
    cJ
    cK
    cL
    cX
    cY
    cR
    cJ
    @0
    @0
    eqid
    #
    mulrcn.j
    mgptopn
    cR
    c.x
    @0
    @1
    cnmpt1mulr.t
    mgpplusg
    wph
    cR
    ctrg
    wcel
    @0
    ctmd
    wcel
    cnmpt1mulr.r
    cR
    @0
    @1
    trgtmd
    syl
    cnmpt1mulr.k
    cnmpt2mulr.l
    cnmpt2mulr.a
    cnmpt2mulr.b
    cnmpt2plusg
end
