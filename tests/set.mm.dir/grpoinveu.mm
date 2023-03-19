include "cgr.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "wreu.mm"
include "grpoidinv2.mm"
include "simpl.mm"
include "reximi.mm"
include "adantl.mm"
include "syl.mm"
include "w3a.mm"
include "eqtr3.mm"
include "grporcan.mm"
include "syl5ib.mm"
include "3exp2.mm"
include "com24.mm"
include "imp41.mm"
include "an32s.mm"
include "expd.mm"
include "ralrimdva.mm"
include "ancld.mm"
include "reximdva.mm"
include "mpd.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "reu8.mm"
include "sylibr.mm"

theorem grpoinveu
  let vy: setvar y
  let cA: class A
  let cU: class U
  let cG: class G
  let cX: class X
  let vz: setvar z
  assume grpinveu.1: |- X = ran G
  assume grpinveu.2: |- U = ( GId ` G )

  disjoint A y
  disjoint G y
  disjoint U y
  disjoint X y
  disjoint y z
  disjoint A z
  disjoint G z
  disjoint U z
  disjoint X z
  assert |- ( ( G e. GrpOp /\ A e. X ) -> E! y e. X ( y G A ) = U )

  proof
    cG
    cgr
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    vy
    cv
    #
    cA
    cG
    co
    #
    cU
    wceq
    #
    vz
    cv
    #
    cA
    cG
    co
    #
    cU
    wceq
    #
    @3
    @6
    wceq
    #
    wi
    #
    vz
    cX
    wral
    #
    wa
    #
    vy
    cX
    wrex
    #
    @5
    vy
    cX
    wreu
    @2
    @5
    vy
    cX
    wrex
    #
    @13
    @2
    cU
    cA
    cG
    co
    cA
    wceq
    cA
    cU
    cG
    co
    cA
    wceq
    wa
    #
    @5
    cA
    @3
    cG
    co
    cU
    wceq
    #
    wa
    #
    vy
    cX
    wrex
    #
    wa
    @14
    vy
    cA
    cU
    cG
    cX
    grpinveu.1
    grpinveu.2
    grpoidinv2
    @18
    @14
    @15
    @17
    @5
    vy
    cX
    @5
    @16
    simpl
    reximi
    adantl
    syl
    @2
    @5
    @12
    vy
    cX
    @2
    @3
    cX
    wcel
    #
    wa
    #
    @5
    @11
    @20
    @5
    @10
    vz
    cX
    @20
    @6
    cX
    wcel
    #
    wa
    @5
    @8
    @9
    @2
    @21
    @19
    @5
    @8
    wa
    #
    @9
    wi
    #
    @0
    @1
    @21
    @19
    @23
    @0
    @19
    @21
    @1
    @23
    @0
    @19
    @21
    @1
    @23
    @22
    @4
    @7
    wceq
    @0
    @19
    @21
    @1
    w3a
    wa
    @9
    @4
    @7
    cU
    eqtr3
    @3
    @6
    cA
    cG
    cX
    grpinveu.1
    grporcan
    syl5ib
    3exp2
    com24
    imp41
    an32s
    expd
    ralrimdva
    ancld
    reximdva
    mpd
    @5
    @8
    vy
    vz
    cX
    @9
    @4
    @7
    cU
    @3
    @6
    cA
    cG
    oveq1
    eqeq1d
    reu8
    sylibr
end
