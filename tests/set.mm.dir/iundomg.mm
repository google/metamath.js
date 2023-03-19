include "ciun.mm"
include "cdom.mm"
include "wbr.mm"
include "cxp.mm"
include "wacn.mm"
include "wcel.mm"
include "c2nd.mm"
include "cres.mm"
include "wfo.mm"
include "iundom2g.mm"
include "acndom2.mm"
include "sylc.mm"
include "iunfo.mm"
include "fodomacn.mm"
include "mpisyl.mm"
include "domtr.mm"
include "syl2anc.mm"

theorem iundomg
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let vy: setvar y
  let vz: setvar z
  assume iunfo.1: |- T = U_ x e. A ( { x } X. B )
  assume iundomg.2: |- ( ph -> U_ x e. A ( C ^m B ) e. AC_ A )
  assume iundomg.3: |- ( ph -> A. x e. A B ~<_ C )
  assume iundomg.4: |- ( ph -> ( A X. C ) e. AC_ U_ x e. A B )

  disjoint A x
  disjoint C x
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B f
  disjoint B g
  disjoint B y
  disjoint B z
  disjoint C f
  disjoint C g
  disjoint C y
  disjoint C z
  disjoint T f
  disjoint T y
  disjoint T z
  disjoint f ph
  assert |- ( ph -> U_ x e. A B ~<_ ( A X. C ) )

  proof
    wph
    vx
    cA
    cB
    ciun
    #
    cT
    cdom
    wbr
    #
    cT
    cA
    cC
    cxp
    #
    cdom
    wbr
    #
    @0
    @2
    cdom
    wbr
    wph
    cT
    @0
    wacn
    #
    wcel
    #
    cT
    @0
    c2nd
    cT
    cres
    #
    wfo
    @1
    wph
    @3
    @2
    @4
    wcel
    @5
    wph
    vx
    cA
    cB
    cC
    cT
    iunfo.1
    iundomg.2
    iundomg.3
    iundom2g
    #
    iundomg.4
    @0
    cT
    @2
    acndom2
    sylc
    vx
    cA
    cB
    cT
    iunfo.1
    iunfo
    cT
    @0
    @6
    fodomacn
    mpisyl
    @7
    @0
    cT
    @2
    domtr
    syl2anc
end
