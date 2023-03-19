include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "chot.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "csm.mm"
include "cva.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "clo.mm"
include "lnopfi.mm"
include "homulcl.mm"
include "mpan2.mm"
include "wa.mm"
include "hvmulcl.mm"
include "hvaddcl.mm"
include "sylan.mm"
include "homval.mm"
include "mp3an2.mm"
include "sylan2.mm"
include "id.mm"
include "ffvelrni.mm"
include "ax-hvdistr1.mm"
include "syl3an.mm"
include "3expb.mm"
include "lnopli.mm"
include "3expa.mm"
include "oveq2d.mm"
include "adantl.mm"
include "adantrl.mm"
include "hvmulcom.mm"
include "syl3an3.mm"
include "eqtr4d.mm"
include "oveqan12d.mm"
include "anandis.mm"
include "3eqtr4rd.mm"
include "exp32.mm"
include "ralrimdv.mm"
include "ralrimivv.mm"
include "ellnop.mm"
include "sylanbrc.mm"

theorem lnopmi
  let cA: class A
  let cT: class T
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume lnopm.1: |- T e. LinOp


  assert |- ( A e. CC -> ( A .op T ) e. LinOp )

  proof
    cA
    cc
    wcel
    #
    chil
    chil
    cA
    cT
    chot
    co
    #
    wf
    #
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
    @1
    cfv
    #
    @3
    @4
    @1
    cfv
    #
    csm
    co
    #
    @6
    @1
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
    #
    vy
    chil
    wral
    vx
    cc
    wral
    @1
    clo
    wcel
    @0
    chil
    chil
    cT
    wf
    #
    @2
    cT
    lnopm.1
    lnopfi
    #
    cA
    cT
    homulcl
    mpan2
    @0
    @14
    vx
    vy
    cc
    chil
    @0
    @3
    cc
    wcel
    #
    @4
    chil
    wcel
    #
    wa
    #
    @13
    vz
    chil
    @0
    @19
    @6
    chil
    wcel
    #
    @13
    @0
    @19
    @20
    wa
    #
    wa
    #
    @8
    cA
    @7
    cT
    cfv
    #
    csm
    co
    #
    @12
    @21
    @0
    @7
    chil
    wcel
    #
    @8
    @24
    wceq
    #
    @19
    @5
    chil
    wcel
    @20
    @25
    @3
    @4
    hvmulcl
    @5
    @6
    hvaddcl
    sylan
    @0
    @15
    @25
    @26
    @16
    cA
    @7
    cT
    homval
    mp3an2
    sylan2
    @22
    cA
    @3
    @4
    cT
    cfv
    #
    csm
    co
    #
    @6
    cT
    cfv
    #
    cva
    co
    #
    csm
    co
    #
    cA
    @28
    csm
    co
    #
    cA
    @29
    csm
    co
    #
    cva
    co
    #
    @24
    @12
    @0
    @19
    @20
    @31
    @34
    wceq
    #
    @0
    @0
    @19
    @28
    chil
    wcel
    #
    @20
    @29
    chil
    wcel
    @35
    @0
    id
    @18
    @17
    @27
    chil
    wcel
    #
    @36
    chil
    chil
    @4
    cT
    @16
    ffvelrni
    #
    @3
    @27
    hvmulcl
    sylan2
    chil
    chil
    @6
    cT
    @16
    ffvelrni
    cA
    @28
    @29
    ax-hvdistr1
    syl3an
    3expb
    @21
    @24
    @31
    wceq
    @0
    @21
    @23
    @30
    cA
    csm
    @17
    @18
    @20
    @23
    @30
    wceq
    @3
    @4
    @6
    cT
    lnopm.1
    lnopli
    3expa
    oveq2d
    adantl
    @0
    @19
    @20
    @12
    @34
    wceq
    @0
    @19
    wa
    #
    @0
    @20
    wa
    @10
    @32
    @11
    @33
    cva
    @39
    @10
    @3
    cA
    @27
    csm
    co
    #
    csm
    co
    #
    @32
    @39
    @9
    @40
    @3
    csm
    @0
    @18
    @9
    @40
    wceq
    #
    @17
    @0
    @15
    @18
    @42
    @16
    cA
    @4
    cT
    homval
    mp3an2
    adantrl
    oveq2d
    @0
    @17
    @18
    @32
    @41
    wceq
    #
    @18
    @0
    @17
    @37
    @43
    @38
    cA
    @3
    @27
    hvmulcom
    syl3an3
    3expb
    eqtr4d
    @0
    @15
    @20
    @11
    @33
    wceq
    @16
    cA
    @6
    cT
    homval
    mp3an2
    oveqan12d
    anandis
    3eqtr4rd
    eqtr4d
    exp32
    ralrimdv
    ralrimivv
    vx
    vy
    vz
    @1
    ellnop
    sylanbrc
end
