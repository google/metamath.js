include "cuo.mm"
include "wcel.mm"
include "chil.mm"
include "ccnv.mm"
include "wfo.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wf1o.mm"
include "unopf1o.mm"
include "f1ocnv.mm"
include "f1ofo.mm"
include "syl.mm"
include "wa.mm"
include "simpl.mm"
include "wf.mm"
include "fof.mm"
include "ffvelrnda.mm"
include "adantrr.mm"
include "adantrl.mm"
include "unop.mm"
include "syl3anc.mm"
include "f1ocnvfv2.mm"
include "oveq12d.mm"
include "sylan.mm"
include "eqtr3d.mm"
include "ralrimivva.mm"
include "elunop.mm"
include "sylanbrc.mm"

theorem cnvunop
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S


  assert |- ( T e. UniOp -> `' T e. UniOp )

  proof
    cT
    cuo
    wcel
    #
    chil
    chil
    cT
    ccnv
    #
    wfo
    #
    vx
    cv
    #
    @1
    cfv
    #
    vy
    cv
    #
    @1
    cfv
    #
    csp
    co
    #
    @3
    @5
    csp
    co
    #
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    @1
    cuo
    wcel
    @0
    chil
    chil
    cT
    wf1o
    #
    @2
    cT
    unopf1o
    #
    @10
    chil
    chil
    @1
    wf1o
    @2
    chil
    chil
    cT
    f1ocnv
    chil
    chil
    @1
    f1ofo
    syl
    syl
    #
    @0
    @9
    vx
    vy
    chil
    chil
    @0
    @3
    chil
    wcel
    #
    @5
    chil
    wcel
    #
    wa
    #
    wa
    #
    @4
    cT
    cfv
    #
    @6
    cT
    cfv
    #
    csp
    co
    #
    @7
    @8
    @16
    @0
    @4
    chil
    wcel
    #
    @6
    chil
    wcel
    #
    @19
    @7
    wceq
    @0
    @15
    simpl
    @0
    @13
    @20
    @14
    @0
    chil
    chil
    @3
    @1
    @0
    @2
    chil
    chil
    @1
    wf
    @12
    chil
    chil
    @1
    fof
    syl
    #
    ffvelrnda
    adantrr
    @0
    @14
    @21
    @13
    @0
    chil
    chil
    @5
    @1
    @22
    ffvelrnda
    adantrl
    @4
    @6
    cT
    unop
    syl3anc
    @0
    @10
    @15
    @19
    @8
    wceq
    @11
    @10
    @15
    wa
    @17
    @3
    @18
    @5
    csp
    @10
    @13
    @17
    @3
    wceq
    @14
    chil
    chil
    @3
    cT
    f1ocnvfv2
    adantrr
    @10
    @14
    @18
    @5
    wceq
    @13
    chil
    chil
    @5
    cT
    f1ocnvfv2
    adantrl
    oveq12d
    sylan
    eqtr3d
    ralrimivva
    vx
    vy
    @1
    elunop
    sylanbrc
end
