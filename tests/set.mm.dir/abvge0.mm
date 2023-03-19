include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "abvfge0.mm"
include "ffvelrnda.mm"
include "cr.mm"
include "elrege0.mm"
include "simprbi.mm"
include "syl.mm"

theorem abvge0
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let c.pl: class .+
  let c.0: class .0.
  let cY: class Y
  let vf: setvar f
  let vr: setvar r
  let c.x: class .x.
  assume abvf.a: |- A = ( AbsVal ` R )
  assume abvf.b: |- B = ( Base ` R )


  assert |- ( ( F e. A /\ X e. B ) -> 0 <_ ( F ` X ) )

  proof
    cF
    cA
    wcel
    #
    cX
    cB
    wcel
    wa
    cX
    cF
    cfv
    #
    cc0
    cpnf
    cico
    co
    #
    wcel
    #
    cc0
    @1
    cle
    wbr
    #
    @0
    cB
    @2
    cX
    cF
    cA
    cB
    cR
    cF
    abvf.a
    abvf.b
    abvfge0
    ffvelrnda
    @3
    @1
    cr
    wcel
    @4
    @1
    elrege0
    simprbi
    syl
end
