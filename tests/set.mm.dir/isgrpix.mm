include "grpbasex.mm"
include "grpplusgx.mm"
include "isgrpi.mm"

theorem isgrpix
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cN: class N
  let c.0: class .0.
  assume isgrpix.a: |- B e. _V
  assume isgrpix.b: |- .+ e. _V
  assume isgrpix.g: |- G = { <. 1 , B >. , <. 2 , .+ >. }
  assume isgrpix.2: |- ( ( x e. B /\ y e. B ) -> ( x .+ y ) e. B )
  assume isgrpix.3: |- ( ( x e. B /\ y e. B /\ z e. B ) -> ( ( x .+ y ) .+ z ) = ( x .+ ( y .+ z ) ) )
  assume isgrpix.z: |- .0. e. B
  assume isgrpix.5: |- ( x e. B -> ( .0. .+ x ) = x )
  assume isgrpix.6: |- ( x e. B -> N e. B )
  assume isgrpix.7: |- ( x e. B -> ( N .+ x ) = .0. )

  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint N y
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint .0. x
  disjoint .0. y
  disjoint .0. z
  assert |- G e. Grp

  proof
    vx
    vy
    vz
    cB
    c.pl
    cG
    cN
    c.0
    cB
    c.pl
    cG
    isgrpix.a
    isgrpix.b
    isgrpix.g
    grpbasex
    cB
    c.pl
    cG
    isgrpix.a
    isgrpix.b
    isgrpix.g
    grpplusgx
    isgrpix.2
    isgrpix.3
    isgrpix.z
    isgrpix.5
    isgrpix.6
    isgrpix.7
    isgrpi
end
