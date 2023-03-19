include "wcel.mm"
include "clmod.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "cmap.mm"
include "co.mm"
include "cfsupp.mm"
include "wbr.mm"
include "w3a.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "cvv.mm"
include "simp3r.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "fsuppres.mm"
include "syl5eqbr.mm"

theorem lindslinindimp2lem3
  let vx: setvar x
  let cB: class B
  let cR: class R
  let cS: class S
  let vf: setvar f
  let cG: class G
  let cM: class M
  let cV: class V
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  let vg: setvar g
  let vs: setvar s
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  assume lindslinind.r: |- R = ( Scalar ` M )
  assume lindslinind.b: |- B = ( Base ` R )
  assume lindslinind.0: |- .0. = ( 0g ` R )
  assume lindslinind.z: |- Z = ( 0g ` M )
  assume lindslinind.y: |- Y = ( ( invg ` R ) ` ( f ` x ) )
  assume lindslinind.g: |- G = ( f |` ( S \ { x } ) )

  disjoint B f
  disjoint M f
  disjoint R f
  disjoint R x
  disjoint f x
  disjoint S f
  disjoint S x
  disjoint Z f
  disjoint .0. f
  disjoint .0. x
  disjoint B g
  disjoint B s
  disjoint B y
  disjoint B z
  disjoint f g
  disjoint f s
  disjoint f y
  disjoint f z
  disjoint g s
  disjoint g y
  disjoint g z
  disjoint s y
  disjoint s z
  disjoint y z
  disjoint M g
  disjoint M s
  disjoint M y
  disjoint M z
  disjoint R z
  disjoint x z
  disjoint S g
  disjoint S s
  disjoint S y
  disjoint S z
  disjoint g x
  disjoint s x
  disjoint x y
  disjoint V g
  disjoint V s
  disjoint V y
  disjoint V z
  disjoint Z g
  disjoint Z s
  disjoint Z y
  disjoint .0. g
  disjoint .0. s
  disjoint .0. y
  disjoint .0. z
  disjoint k x
  assert |- ( ( ( S e. V /\ M e. LMod ) /\ ( S C_ ( Base ` M ) /\ x e. S ) /\ ( f e. ( B ^m S ) /\ f finSupp .0. ) ) -> G finSupp .0. )

  proof
    cS
    cV
    wcel
    cM
    clmod
    wcel
    wa
    #
    cS
    cM
    cbs
    cfv
    wss
    vx
    cv
    #
    cS
    wcel
    wa
    #
    vf
    cv
    #
    cB
    cS
    cmap
    co
    wcel
    #
    @3
    c.0
    cfsupp
    wbr
    #
    wa
    w3a
    #
    cG
    @3
    cS
    @1
    csn
    cdif
    #
    cres
    c.0
    cfsupp
    lindslinind.g
    @6
    @3
    cvv
    @7
    c.0
    @0
    @2
    @4
    @5
    simp3r
    c.0
    cvv
    wcel
    @6
    c.0
    cR
    c0g
    cfv
    cvv
    lindslinind.0
    cR
    c0g
    fvex
    eqeltri
    a1i
    fsuppres
    syl5eqbr
end
