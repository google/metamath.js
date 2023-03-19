include "cbs.mm"
include "cfv.mm"
include "cplusg.mm"
include "c0g.mm"
include "eqid.mm"
include "eleqtrd.mm"
include "cv.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "wa.mm"
include "adantr.mm"
include "oveqd.mm"
include "eqtr3d.mm"
include "syldan.mm"
include "ismgmid2.mm"

theorem grpidd
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let c.0: class .0.
  assume grpidd.b: |- ( ph -> B = ( Base ` G ) )
  assume grpidd.p: |- ( ph -> .+ = ( +g ` G ) )
  assume grpidd.z: |- ( ph -> .0. e. B )
  assume grpidd.i: |- ( ( ph /\ x e. B ) -> ( .0. .+ x ) = x )
  assume grpidd.j: |- ( ( ph /\ x e. B ) -> ( x .+ .0. ) = x )

  disjoint G x
  disjoint ph x
  disjoint .0. x
  assert |- ( ph -> .0. = ( 0g ` G ) )

  proof
    wph
    vx
    cG
    cbs
    cfv
    #
    cG
    cplusg
    cfv
    #
    c.0
    cG
    cG
    c0g
    cfv
    #
    @0
    eqid
    @2
    eqid
    @1
    eqid
    wph
    c.0
    cB
    @0
    grpidd.z
    grpidd.b
    eleqtrd
    wph
    vx
    cv
    #
    @0
    wcel
    #
    @3
    cB
    wcel
    #
    c.0
    @3
    @1
    co
    #
    @3
    wceq
    wph
    @5
    @4
    wph
    cB
    @0
    @3
    grpidd.b
    eleq2d
    biimpar
    #
    wph
    @5
    wa
    #
    c.0
    @3
    c.pl
    co
    @6
    @3
    @8
    c.pl
    @1
    c.0
    @3
    wph
    c.pl
    @1
    wceq
    @5
    grpidd.p
    adantr
    #
    oveqd
    grpidd.i
    eqtr3d
    syldan
    wph
    @4
    @5
    @3
    c.0
    @1
    co
    #
    @3
    wceq
    @7
    @8
    @3
    c.0
    c.pl
    co
    @10
    @3
    @8
    c.pl
    @1
    @3
    c.0
    @9
    oveqd
    grpidd.j
    eqtr3d
    syldan
    ismgmid2
end
