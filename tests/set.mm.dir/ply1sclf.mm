include "crg.mm"
include "wcel.mm"
include "cid.mm"
include "cfv.mm"
include "ply1sca2.mm"
include "ply1ring.mm"
include "ply1lmod.mm"
include "cbs.mm"
include "c1.mm"
include "df-base.mm"
include "strfvi.mm"
include "asclf.mm"

theorem ply1sclf
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cK: class K
  let vx: setvar x
  let vy: setvar y
  let cX: class X
  let c.0: class .0.
  assume ply1scl.p: |- P = ( Poly1 ` R )
  assume ply1scl.a: |- A = ( algSc ` P )
  assume coe1scl.k: |- K = ( Base ` R )
  assume ply1sclf.b: |- B = ( Base ` P )


  assert |- ( R e. Ring -> A : K --> B )

  proof
    cR
    crg
    wcel
    cA
    cB
    cR
    cid
    cfv
    cK
    cP
    ply1scl.a
    cP
    cR
    ply1scl.p
    ply1sca2
    cP
    cR
    ply1scl.p
    ply1ring
    cP
    cR
    ply1scl.p
    ply1lmod
    cR
    cbs
    c1
    cK
    df-base
    coe1scl.k
    strfvi
    ply1sclf.b
    asclf
end
