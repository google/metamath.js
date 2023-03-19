include "c0g.mm"
include "cfv.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "oveqd.mm"
include "wcel.mm"
include "cv.mm"
include "wral.mm"
include "ralrimiva.mm"
include "oveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "eqtr3d.mm"
include "cgrp.mm"
include "cbs.mm"
include "wb.mm"
include "eleqtrd.mm"
include "eqid.mm"
include "grpid.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "eqcomd.mm"

theorem grpidd2
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let c.0: class .0.
  assume grpidd2.b: |- ( ph -> B = ( Base ` G ) )
  assume grpidd2.p: |- ( ph -> .+ = ( +g ` G ) )
  assume grpidd2.z: |- ( ph -> .0. e. B )
  assume grpidd2.i: |- ( ( ph /\ x e. B ) -> ( .0. .+ x ) = x )
  assume grpidd2.j: |- ( ph -> G e. Grp )

  disjoint B x
  disjoint .+ x
  disjoint ph x
  disjoint .0. x
  assert |- ( ph -> .0. = ( 0g ` G ) )

  proof
    wph
    cG
    c0g
    cfv
    #
    c.0
    wph
    c.0
    c.0
    cG
    cplusg
    cfv
    #
    co
    #
    c.0
    wceq
    #
    @0
    c.0
    wceq
    #
    wph
    c.0
    c.0
    c.pl
    co
    #
    @2
    c.0
    wph
    c.pl
    @1
    c.0
    c.0
    grpidd2.p
    oveqd
    wph
    c.0
    cB
    wcel
    c.0
    vx
    cv
    #
    c.pl
    co
    #
    @6
    wceq
    #
    vx
    cB
    wral
    @5
    c.0
    wceq
    #
    grpidd2.z
    wph
    @8
    vx
    cB
    grpidd2.i
    ralrimiva
    @8
    @9
    vx
    c.0
    cB
    @6
    c.0
    wceq
    #
    @7
    @5
    @6
    c.0
    @6
    c.0
    c.0
    c.pl
    oveq2
    @10
    id
    eqeq12d
    rspcv
    sylc
    eqtr3d
    wph
    cG
    cgrp
    wcel
    c.0
    cG
    cbs
    cfv
    #
    wcel
    @3
    @4
    wb
    grpidd2.j
    wph
    c.0
    cB
    @11
    grpidd2.z
    grpidd2.b
    eleqtrd
    @11
    @1
    cG
    c.0
    @0
    @11
    eqid
    @1
    eqid
    @0
    eqid
    grpid
    syl2anc
    mpbid
    eqcomd
end
