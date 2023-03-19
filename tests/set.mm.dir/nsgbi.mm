include "cnsg.mm"
include "cfv.mm"
include "wcel.mm"
include "co.mm"
include "wb.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "csubg.mm"
include "isnsg.mm"
include "simprbi.mm"
include "wceq.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "oveq2.mm"
include "bibi12d.mm"
include "rspc2v.mm"
include "syl5com.mm"
include "3impib.mm"

theorem nsgbi
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let cG: class G
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vb: setvar b
  let vg: setvar g
  let vp: setvar p
  let vs: setvar s
  let vz: setvar z
  assume isnsg.1: |- X = ( Base ` G )
  assume isnsg.2: |- .+ = ( +g ` G )


  assert |- ( ( S e. ( NrmSGrp ` G ) /\ A e. X /\ B e. X ) -> ( ( A .+ B ) e. S <-> ( B .+ A ) e. S ) )

  proof
    cS
    cG
    cnsg
    cfv
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cA
    cB
    c.pl
    co
    #
    cS
    wcel
    #
    cB
    cA
    c.pl
    co
    #
    cS
    wcel
    #
    wb
    #
    @0
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    #
    cS
    wcel
    #
    @9
    @8
    c.pl
    co
    #
    cS
    wcel
    #
    wb
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    @1
    @2
    wa
    @7
    @0
    cS
    cG
    csubg
    cfv
    wcel
    @15
    vx
    vy
    c.pl
    cS
    cG
    cX
    isnsg.1
    isnsg.2
    isnsg
    simprbi
    @14
    @7
    cA
    @9
    c.pl
    co
    #
    cS
    wcel
    #
    @9
    cA
    c.pl
    co
    #
    cS
    wcel
    #
    wb
    vx
    vy
    cA
    cB
    cX
    cX
    @8
    cA
    wceq
    #
    @11
    @17
    @13
    @19
    @20
    @10
    @16
    cS
    @8
    cA
    @9
    c.pl
    oveq1
    eleq1d
    @20
    @12
    @18
    cS
    @8
    cA
    @9
    c.pl
    oveq2
    eleq1d
    bibi12d
    @9
    cB
    wceq
    #
    @17
    @4
    @19
    @6
    @21
    @16
    @3
    cS
    @9
    cB
    cA
    c.pl
    oveq2
    eleq1d
    @21
    @18
    @5
    cS
    @9
    cB
    cA
    c.pl
    oveq1
    eleq1d
    bibi12d
    rspc2v
    syl5com
    3impib
end
