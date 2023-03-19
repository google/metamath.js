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
include "cnmpt1plusg.mm"

theorem cnmpt1mulr
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cJ: class J
  let cK: class K
  let cX: class X
  let vy: setvar y
  let cY: class Y
  assume mulrcn.j: |- J = ( TopOpen ` R )
  assume cnmpt1mulr.t: |- .x. = ( .r ` R )
  assume cnmpt1mulr.r: |- ( ph -> R e. TopRing )
  assume cnmpt1mulr.k: |- ( ph -> K e. ( TopOn ` X ) )
  assume cnmpt1mulr.a: |- ( ph -> ( x e. X |-> A ) e. ( K Cn J ) )
  assume cnmpt1mulr.b: |- ( ph -> ( x e. X |-> B ) e. ( K Cn J ) )

  disjoint J x
  disjoint K x
  disjoint ph x
  disjoint R x
  disjoint X x
  disjoint x y
  disjoint J y
  disjoint ph y
  disjoint R y
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( ph -> ( x e. X |-> ( A .x. B ) ) e. ( K Cn J ) )

  proof
    wph
    vx
    cA
    cB
    c.x
    cR
    cmgp
    cfv
    #
    cJ
    cK
    cX
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
    cnmpt1mulr.a
    cnmpt1mulr.b
    cnmpt1plusg
end
