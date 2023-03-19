include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cz.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cmpt.mm"
include "wf.mm"
include "caddc.mm"
include "cfv.mm"
include "cmul.mm"
include "wceq.mm"
include "wral.mm"
include "zring.mm"
include "cghm.mm"
include "expclzlem.mm"
include "3expa.mm"
include "eqid.mm"
include "fmptd.mm"
include "expaddz.mm"
include "zaddcl.mm"
include "adantl.mm"
include "oveq2.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "oveqan12d.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "cgrp.mm"
include "zringgrp.mm"
include "ccnfld.mm"
include "crg.mm"
include "cnring.mm"
include "cnfldbas.mm"
include "cnfld0.mm"
include "cndrng.mm"
include "drngui.mm"
include "cress.mm"
include "cmgp.mm"
include "oveq1i.mm"
include "eqtri.mm"
include "unitgrp.mm"
include "ax-mp.mm"
include "pm3.2i.mm"
include "zringbas.mm"
include "wss.mm"
include "cbs.mm"
include "difss.mm"
include "mgpbas.mm"
include "ressbas2.mm"
include "zringplusg.mm"
include "cvv.mm"
include "cplusg.mm"
include "cui.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cnfldmul.mm"
include "mgpplusg.mm"
include "ressplusg.mm"
include "isghm.mm"
include "mpbiran.mm"
include "sylanbrc.mm"

theorem expghm
  let vx: setvar x
  let cA: class A
  let cU: class U
  let cM: class M
  let vy: setvar y
  let vz: setvar z
  assume expghm.m: |- M = ( mulGrp ` CCfld )
  assume expghm.u: |- U = ( M |`s ( CC \ { 0 } ) )

  disjoint A x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint U y
  disjoint U z
  assert |- ( ( A e. CC /\ A =/= 0 ) -> ( x e. ZZ |-> ( A ^ x ) ) e. ( ZZring GrpHom U ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    #
    cz
    cc
    cc0
    csn
    #
    cdif
    #
    vx
    cz
    cA
    vx
    cv
    #
    cexp
    co
    #
    cmpt
    #
    wf
    #
    vy
    cv
    #
    vz
    cv
    #
    caddc
    co
    #
    @7
    cfv
    #
    @9
    @7
    cfv
    #
    @10
    @7
    cfv
    #
    cmul
    co
    #
    wceq
    #
    vz
    cz
    wral
    vy
    cz
    wral
    #
    @7
    zring
    cU
    cghm
    co
    wcel
    #
    @2
    vx
    cz
    @6
    @4
    @7
    @0
    @1
    @5
    cz
    wcel
    @6
    @4
    wcel
    cA
    @5
    expclzlem
    3expa
    @7
    eqid
    #
    fmptd
    @2
    @16
    vy
    vz
    cz
    cz
    @2
    @9
    cz
    wcel
    #
    @10
    cz
    wcel
    #
    wa
    #
    wa
    #
    cA
    @11
    cexp
    co
    #
    cA
    @9
    cexp
    co
    #
    cA
    @10
    cexp
    co
    #
    cmul
    co
    #
    @12
    @15
    cA
    @9
    @10
    expaddz
    @23
    @11
    cz
    wcel
    #
    @12
    @24
    wceq
    @22
    @28
    @2
    @9
    @10
    zaddcl
    adantl
    vx
    @11
    @6
    @24
    cz
    @7
    @5
    @11
    cA
    cexp
    oveq2
    @19
    cA
    @11
    cexp
    ovex
    fvmpt
    syl
    @22
    @15
    @27
    wceq
    @2
    @20
    @21
    @13
    @25
    @14
    @26
    cmul
    vx
    @9
    @6
    @25
    cz
    @7
    @5
    @9
    cA
    cexp
    oveq2
    @19
    cA
    @9
    cexp
    ovex
    fvmpt
    vx
    @10
    @6
    @26
    cz
    @7
    @5
    @10
    cA
    cexp
    oveq2
    @19
    cA
    @10
    cexp
    ovex
    fvmpt
    oveqan12d
    adantl
    3eqtr4d
    ralrimivva
    @18
    zring
    cgrp
    wcel
    #
    cU
    cgrp
    wcel
    #
    wa
    @8
    @17
    wa
    @29
    @30
    zringgrp
    ccnfld
    crg
    wcel
    @30
    cnring
    ccnfld
    @4
    cU
    cc
    ccnfld
    cc0
    cnfldbas
    cnfld0
    cndrng
    drngui
    #
    cU
    cM
    @4
    cress
    co
    ccnfld
    cmgp
    cfv
    #
    @4
    cress
    co
    expghm.u
    cM
    @32
    @4
    cress
    expghm.m
    oveq1i
    eqtri
    unitgrp
    ax-mp
    pm3.2i
    vz
    vy
    caddc
    cmul
    zring
    cU
    @7
    cz
    @4
    zringbas
    @4
    cc
    wss
    @4
    cU
    cbs
    cfv
    wceq
    cc
    @3
    difss
    @4
    cc
    cU
    cM
    expghm.u
    cc
    ccnfld
    cM
    expghm.m
    cnfldbas
    mgpbas
    ressbas2
    ax-mp
    zringplusg
    @4
    cvv
    wcel
    cmul
    cU
    cplusg
    cfv
    wceq
    @4
    ccnfld
    cui
    cfv
    cvv
    @31
    ccnfld
    cui
    fvex
    eqeltri
    @4
    cmul
    cM
    cU
    cvv
    expghm.u
    ccnfld
    cmul
    cM
    expghm.m
    cnfldmul
    mgpplusg
    ressplusg
    ax-mp
    isghm
    mpbiran
    sylanbrc
end
