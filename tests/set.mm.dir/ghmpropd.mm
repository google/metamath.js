include "cghm.mm"
include "co.mm"
include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cmhm.mm"
include "grppropd.mm"
include "anbi12d.mm"
include "mhmpropd.mm"
include "eleq2d.mm"
include "ghmgrp1.mm"
include "ghmgrp2.mm"
include "jca.mm"
include "ghmmhmb.mm"
include "biadan2.mm"
include "3bitr4g.mm"
include "eqrdv.mm"

theorem ghmpropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let vf: setvar f
  assume ghmpropd.a: |- ( ph -> B = ( Base ` J ) )
  assume ghmpropd.b: |- ( ph -> C = ( Base ` K ) )
  assume ghmpropd.c: |- ( ph -> B = ( Base ` L ) )
  assume ghmpropd.d: |- ( ph -> C = ( Base ` M ) )
  assume ghmpropd.e: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( +g ` J ) y ) = ( x ( +g ` L ) y ) )
  assume ghmpropd.f: |- ( ( ph /\ ( x e. C /\ y e. C ) ) -> ( x ( +g ` K ) y ) = ( x ( +g ` M ) y ) )

  disjoint x y
  disjoint J x
  disjoint J y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint M x
  disjoint M y
  disjoint ph x
  disjoint ph y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint f x
  disjoint f y
  disjoint J f
  disjoint K f
  disjoint L f
  disjoint M f
  disjoint f ph
  assert |- ( ph -> ( J GrpHom K ) = ( L GrpHom M ) )

  proof
    wph
    vf
    cJ
    cK
    cghm
    co
    #
    cL
    cM
    cghm
    co
    #
    wph
    cJ
    cgrp
    wcel
    #
    cK
    cgrp
    wcel
    #
    wa
    #
    vf
    cv
    #
    cJ
    cK
    cmhm
    co
    #
    wcel
    #
    wa
    cL
    cgrp
    wcel
    #
    cM
    cgrp
    wcel
    #
    wa
    #
    @5
    cL
    cM
    cmhm
    co
    #
    wcel
    #
    wa
    @5
    @0
    wcel
    #
    @5
    @1
    wcel
    #
    wph
    @4
    @10
    @7
    @12
    wph
    @2
    @8
    @3
    @9
    wph
    vx
    vy
    cB
    cJ
    cL
    ghmpropd.a
    ghmpropd.c
    ghmpropd.e
    grppropd
    wph
    vx
    vy
    cC
    cK
    cM
    ghmpropd.b
    ghmpropd.d
    ghmpropd.f
    grppropd
    anbi12d
    wph
    @6
    @11
    @5
    wph
    vx
    vy
    cB
    cC
    cJ
    cK
    cL
    cM
    ghmpropd.a
    ghmpropd.b
    ghmpropd.c
    ghmpropd.d
    ghmpropd.e
    ghmpropd.f
    mhmpropd
    eleq2d
    anbi12d
    @13
    @4
    @7
    @13
    @2
    @3
    cJ
    cK
    @5
    ghmgrp1
    cJ
    cK
    @5
    ghmgrp2
    jca
    @4
    @0
    @6
    @5
    cJ
    cK
    ghmmhmb
    eleq2d
    biadan2
    @14
    @10
    @12
    @14
    @8
    @9
    cL
    cM
    @5
    ghmgrp1
    cL
    cM
    @5
    ghmgrp2
    jca
    @10
    @1
    @11
    @5
    cL
    cM
    ghmmhmb
    eleq2d
    biadan2
    3bitr4g
    eqrdv
end
