include "wrel.mm"
include "wfn.mm"
include "crn.mm"
include "wceq.mm"
include "wa.mm"
include "ctpos.mm"
include "ccnv.mm"
include "wfo.mm"
include "tposfn2.mm"
include "adantrd.mm"
include "cdm.mm"
include "fndm.mm"
include "releqd.mm"
include "biimparc.mm"
include "rntpos.mm"
include "syl.mm"
include "eqeq1d.mm"
include "biimprd.mm"
include "expimpd.mm"
include "jcad.mm"
include "df-fo.mm"
include "3imtr4g.mm"

theorem tposfo2
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z
  let cG: class G


  assert |- ( Rel A -> ( F : A -onto-> B -> tpos F : `' A -onto-> B ) )

  proof
    cA
    wrel
    #
    cF
    cA
    wfn
    #
    cF
    crn
    #
    cB
    wceq
    #
    wa
    #
    cF
    ctpos
    #
    cA
    ccnv
    #
    wfn
    #
    @5
    crn
    #
    cB
    wceq
    #
    wa
    cA
    cB
    cF
    wfo
    @6
    cB
    @5
    wfo
    @0
    @4
    @7
    @9
    @0
    @1
    @7
    @3
    cA
    cF
    tposfn2
    adantrd
    @0
    @1
    @3
    @9
    @0
    @1
    wa
    #
    @9
    @3
    @10
    @8
    @2
    cB
    @10
    cF
    cdm
    #
    wrel
    #
    @8
    @2
    wceq
    @1
    @12
    @0
    @1
    @11
    cA
    cA
    cF
    fndm
    releqd
    biimparc
    cF
    rntpos
    syl
    eqeq1d
    biimprd
    expimpd
    jcad
    cA
    cB
    cF
    df-fo
    @6
    cB
    @5
    df-fo
    3imtr4g
end
