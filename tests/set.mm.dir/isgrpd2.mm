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
include "isgrpd2e.mm"

theorem isgrpd2
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cN: class N
  let c.0: class .0.
  let vy: setvar y
  assume isgrpd2.b: |- ( ph -> B = ( Base ` G ) )
  assume isgrpd2.p: |- ( ph -> .+ = ( +g ` G ) )
  assume isgrpd2.z: |- ( ph -> .0. = ( 0g ` G ) )
  assume isgrpd2.g: |- ( ph -> G e. Mnd )
  assume isgrpd2.n: |- ( ( ph /\ x e. B ) -> N e. B )
  assume isgrpd2.j: |- ( ( ph /\ x e. B ) -> ( N .+ x ) = .0. )

  disjoint .+ x
  disjoint B x
  disjoint G x
  disjoint ph x
  disjoint x y
  disjoint .+ y
  disjoint .0. y
  disjoint B y
  disjoint G y
  disjoint ph y
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
    isgrpd2.b
    isgrpd2.p
    isgrpd2.z
    isgrpd2.g
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
    isgrpd2.n
    isgrpd2.j
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
    isgrpd2e
end
