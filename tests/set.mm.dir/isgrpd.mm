include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "isgrpde.mm"

theorem isgrpd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cN: class N
  let c.0: class .0.
  assume isgrpd.b: |- ( ph -> B = ( Base ` G ) )
  assume isgrpd.p: |- ( ph -> .+ = ( +g ` G ) )
  assume isgrpd.c: |- ( ( ph /\ x e. B /\ y e. B ) -> ( x .+ y ) e. B )
  assume isgrpd.a: |- ( ( ph /\ ( x e. B /\ y e. B /\ z e. B ) ) -> ( ( x .+ y ) .+ z ) = ( x .+ ( y .+ z ) ) )
  assume isgrpd.z: |- ( ph -> .0. e. B )
  assume isgrpd.i: |- ( ( ph /\ x e. B ) -> ( .0. .+ x ) = x )
  assume isgrpd.n: |- ( ( ph /\ x e. B ) -> N e. B )
  assume isgrpd.j: |- ( ( ph /\ x e. B ) -> ( N .+ x ) = .0. )

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
  disjoint N y
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint G x
  disjoint G y
  disjoint G z
  assert |- ( ph -> G e. Grp )

  proof
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
    wph
    vx
    cv
    #
    cB
    wcel
    wa
    cN
    cB
    wcel
    cN
    @0
    c.pl
    co
    #
    c.0
    wceq
    #
    vy
    cv
    #
    @0
    c.pl
    co
    #
    c.0
    wceq
    #
    vy
    cB
    wrex
    isgrpd.n
    isgrpd.j
    @5
    @2
    vy
    cN
    cB
    @3
    cN
    wceq
    @4
    @1
    c.0
    @3
    cN
    @0
    c.pl
    oveq1
    eqeq1d
    rspcev
    syl2anc
    isgrpde
end
