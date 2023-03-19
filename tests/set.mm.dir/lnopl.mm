include "clo.mm"
include "wcel.mm"
include "cc.mm"
include "chil.mm"
include "wa.mm"
include "csm.mm"
include "co.mm"
include "cva.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "cv.mm"
include "wral.mm"
include "w3a.mm"
include "wf.mm"
include "ellnop.mm"
include "simprbi.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "rspc3v.mm"
include "syl5.mm"
include "3expb.mm"
include "impcom.mm"
include "anassrs.mm"

theorem lnopl
  let cA: class A
  let cB: class B
  let cC: class C
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cS: class S


  assert |- ( ( ( T e. LinOp /\ A e. CC ) /\ ( B e. ~H /\ C e. ~H ) ) -> ( T ` ( ( A .h B ) +h C ) ) = ( ( A .h ( T ` B ) ) +h ( T ` C ) ) )

  proof
    cT
    clo
    wcel
    #
    cA
    cc
    wcel
    #
    cB
    chil
    wcel
    #
    cC
    chil
    wcel
    #
    wa
    #
    cA
    cB
    csm
    co
    #
    cC
    cva
    co
    #
    cT
    cfv
    #
    cA
    cB
    cT
    cfv
    #
    csm
    co
    #
    cC
    cT
    cfv
    #
    cva
    co
    #
    wceq
    #
    @1
    @4
    wa
    @0
    @12
    @1
    @2
    @3
    @0
    @12
    wi
    @0
    vx
    cv
    #
    vy
    cv
    #
    csm
    co
    #
    vz
    cv
    #
    cva
    co
    #
    cT
    cfv
    #
    @13
    @14
    cT
    cfv
    #
    csm
    co
    #
    @16
    cT
    cfv
    #
    cva
    co
    #
    wceq
    #
    vz
    chil
    wral
    vy
    chil
    wral
    vx
    cc
    wral
    #
    @1
    @2
    @3
    w3a
    @12
    @0
    chil
    chil
    cT
    wf
    @24
    vx
    vy
    vz
    cT
    ellnop
    simprbi
    @23
    @12
    cA
    @14
    csm
    co
    #
    @16
    cva
    co
    #
    cT
    cfv
    #
    cA
    @19
    csm
    co
    #
    @21
    cva
    co
    #
    wceq
    @5
    @16
    cva
    co
    #
    cT
    cfv
    #
    @9
    @21
    cva
    co
    #
    wceq
    vx
    vy
    vz
    cA
    cB
    cC
    cc
    chil
    chil
    @13
    cA
    wceq
    #
    @18
    @27
    @22
    @29
    @33
    @17
    @26
    cT
    @33
    @15
    @25
    @16
    cva
    @13
    cA
    @14
    csm
    oveq1
    oveq1d
    fveq2d
    @33
    @20
    @28
    @21
    cva
    @13
    cA
    @19
    csm
    oveq1
    oveq1d
    eqeq12d
    @14
    cB
    wceq
    #
    @27
    @31
    @29
    @32
    @34
    @26
    @30
    cT
    @34
    @25
    @5
    @16
    cva
    @14
    cB
    cA
    csm
    oveq2
    oveq1d
    fveq2d
    @34
    @28
    @9
    @21
    cva
    @34
    @19
    @8
    cA
    csm
    @14
    cB
    cT
    fveq2
    oveq2d
    oveq1d
    eqeq12d
    @16
    cC
    wceq
    #
    @31
    @7
    @32
    @11
    @35
    @30
    @6
    cT
    @16
    cC
    @5
    cva
    oveq2
    fveq2d
    @35
    @21
    @10
    @9
    cva
    @16
    cC
    cT
    fveq2
    oveq2d
    eqeq12d
    rspc3v
    syl5
    3expb
    impcom
    anassrs
end
