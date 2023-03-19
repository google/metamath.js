include "crngo.mm"
include "wcel.mm"
include "crnghom.mm"
include "co.mm"
include "w3a.mm"
include "rngohomf.mm"
include "ffvelrnda.mm"

theorem rngohomcl
  let cA: class A
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume rnghomf.1: |- G = ( 1st ` R )
  assume rnghomf.2: |- X = ran G
  assume rnghomf.3: |- J = ( 1st ` S )
  assume rnghomf.4: |- Y = ran J


  assert |- ( ( ( R e. RingOps /\ S e. RingOps /\ F e. ( R RngHom S ) ) /\ A e. X ) -> ( F ` A ) e. Y )

  proof
    cR
    crngo
    wcel
    cS
    crngo
    wcel
    cF
    cR
    cS
    crnghom
    co
    wcel
    w3a
    cX
    cY
    cA
    cF
    cR
    cS
    cF
    cG
    cJ
    cX
    cY
    rnghomf.1
    rnghomf.2
    rnghomf.3
    rnghomf.4
    rngohomf
    ffvelrnda
end
