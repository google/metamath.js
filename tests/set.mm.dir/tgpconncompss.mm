include "ctgp.mm"
include "wcel.mm"
include "csubg.mm"
include "cfv.mm"
include "w3a.mm"
include "ctopon.mm"
include "ccld.mm"
include "cin.mm"
include "wss.mm"
include "tgptopon.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "opnsubg.mm"
include "elind.mm"
include "subg0cl.mm"
include "3ad2ant2.mm"
include "conncompclo.mm"
include "syl3anc.mm"

theorem tgpconncompss
  let vx: setvar x
  let cS: class S
  let cT: class T
  let cG: class G
  let cJ: class J
  let cX: class X
  let c.0: class .0.
  let vy: setvar y
  let vz: setvar z
  let c.sm: class .~
  let vg: setvar g
  let cA: class A
  let vw: setvar w
  assume tgpconncomp.x: |- X = ( Base ` G )
  assume tgpconncomp.z: |- .0. = ( 0g ` G )
  assume tgpconncomp.j: |- J = ( TopOpen ` G )
  assume tgpconncomp.s: |- S = U. { x e. ~P X | ( .0. e. x /\ ( J |`t x ) e. Conn ) }

  disjoint .0. x
  disjoint J x
  disjoint G x
  disjoint X x
  disjoint y z
  disjoint .~ y
  disjoint .~ z
  disjoint x z
  disjoint .0. z
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint J w
  disjoint J y
  disjoint J z
  disjoint S y
  disjoint S z
  disjoint g w
  disjoint G g
  disjoint G w
  disjoint G y
  disjoint G z
  disjoint X g
  disjoint X w
  disjoint X y
  disjoint X z
  assert |- ( ( G e. TopGrp /\ T e. ( SubGrp ` G ) /\ T e. J ) -> S C_ T )

  proof
    cG
    ctgp
    wcel
    #
    cT
    cG
    csubg
    cfv
    wcel
    #
    cT
    cJ
    wcel
    #
    w3a
    #
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cT
    cJ
    cJ
    ccld
    cfv
    #
    cin
    wcel
    c.0
    cT
    wcel
    #
    cS
    cT
    wss
    @0
    @1
    @4
    @2
    cG
    cJ
    cX
    tgpconncomp.j
    tgpconncomp.x
    tgptopon
    3ad2ant1
    @3
    cJ
    @5
    cT
    @0
    @1
    @2
    simp3
    cT
    cG
    cJ
    tgpconncomp.j
    opnsubg
    elind
    @1
    @0
    @6
    @2
    cT
    cG
    c.0
    tgpconncomp.z
    subg0cl
    3ad2ant2
    vx
    c.0
    cS
    cT
    cJ
    cX
    tgpconncomp.s
    conncompclo
    syl3anc
end
