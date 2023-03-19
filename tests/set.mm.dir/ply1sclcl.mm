include "crg.mm"
include "wcel.mm"
include "ply1sclf.mm"
include "ffvelrnda.mm"

theorem ply1sclcl
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let cK: class K
  let vx: setvar x
  let vy: setvar y
  let cX: class X
  let c.0: class .0.
  assume ply1scl.p: |- P = ( Poly1 ` R )
  assume ply1scl.a: |- A = ( algSc ` P )
  assume coe1scl.k: |- K = ( Base ` R )
  assume ply1sclf.b: |- B = ( Base ` P )


  assert |- ( ( R e. Ring /\ S e. K ) -> ( A ` S ) e. B )

  proof
    cR
    crg
    wcel
    cK
    cB
    cS
    cA
    cA
    cB
    cP
    cR
    cK
    ply1scl.p
    ply1scl.a
    coe1scl.k
    ply1sclf.b
    ply1sclf
    ffvelrnda
end
