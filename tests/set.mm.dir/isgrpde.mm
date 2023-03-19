include "grpridd.mm"
include "grpidd.mm"
include "ismndd.mm"
include "isgrpd2e.mm"

theorem isgrpde
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let c.0: class .0.
  let cN: class N
  assume isgrpd.b: |- ( ph -> B = ( Base ` G ) )
  assume isgrpd.p: |- ( ph -> .+ = ( +g ` G ) )
  assume isgrpd.c: |- ( ( ph /\ x e. B /\ y e. B ) -> ( x .+ y ) e. B )
  assume isgrpd.a: |- ( ( ph /\ ( x e. B /\ y e. B /\ z e. B ) ) -> ( ( x .+ y ) .+ z ) = ( x .+ ( y .+ z ) ) )
  assume isgrpd.z: |- ( ph -> .0. e. B )
  assume isgrpd.i: |- ( ( ph /\ x e. B ) -> ( .0. .+ x ) = x )
  assume isgrpde.n: |- ( ( ph /\ x e. B ) -> E. y e. B ( y .+ x ) = .0. )

  disjoint x y
  disjoint x z
  disjoint .+ x
  disjoint y z
  disjoint .+ y
  disjoint .+ z
  disjoint .0. x
  disjoint .0. y
  disjoint .0. z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint N y
  assert |- ( ph -> G e. Grp )

  proof
    wph
    vx
    vy
    cB
    c.pl
    cG
    c.0
    isgrpd.b
    isgrpd.p
    wph
    vx
    cB
    c.pl
    cG
    c.0
    isgrpd.b
    isgrpd.p
    isgrpd.z
    isgrpd.i
    wph
    vx
    vy
    vz
    cB
    c.pl
    c.0
    isgrpd.c
    isgrpd.z
    isgrpd.i
    isgrpd.a
    isgrpde.n
    grpridd
    #
    grpidd
    wph
    vx
    vy
    vz
    cB
    c.pl
    cG
    c.0
    isgrpd.b
    isgrpd.p
    isgrpd.c
    isgrpd.a
    isgrpd.z
    isgrpd.i
    @0
    ismndd
    isgrpde.n
    isgrpd2e
end
