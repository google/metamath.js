include "wcel.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "wf.mm"
include "cr.mm"
include "wss.mm"
include "abvfge0.mm"
include "rge0ssre.mm"
include "fss.mm"
include "sylancl.mm"

theorem abvf
  let cA: class A
  let cB: class B
  let cR: class R
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let c.pl: class .+
  let c.0: class .0.
  let cY: class Y
  let vf: setvar f
  let vr: setvar r
  let c.x: class .x.
  let cX: class X
  assume abvf.a: |- A = ( AbsVal ` R )
  assume abvf.b: |- B = ( Base ` R )


  assert |- ( F e. A -> F : B --> RR )

  proof
    cF
    cA
    wcel
    cB
    cc0
    cpnf
    cico
    co
    #
    cF
    wf
    @0
    cr
    wss
    cB
    cr
    cF
    wf
    cA
    cB
    cR
    cF
    abvf.a
    abvf.b
    abvfge0
    rge0ssre
    cB
    @0
    cr
    cF
    fss
    sylancl
end
