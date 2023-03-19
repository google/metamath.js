include "cho.mm"
include "wcel.mm"
include "ch0o.mm"
include "ccom.mm"
include "cleo.mm"
include "wbr.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "cle.mm"
include "chil.mm"
include "wral.mm"
include "wa.mm"
include "hmopf.mm"
include "ffvelrnda.mm"
include "hiidge0.mm"
include "syl.mm"
include "wceq.mm"
include "simpl.mm"
include "simpr.mm"
include "hmop.mm"
include "syl3anc.mm"
include "wf.mm"
include "fvco3.mm"
include "sylan.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "breqtrd.mm"
include "ralrimiva.mm"
include "wb.mm"
include "eqid.mm"
include "hmopco.mm"
include "mp3an3.mm"
include "anidms.mm"
include "leoppos.mm"
include "mpbird.mm"

theorem leopsq
  let cT: class T
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let vt: setvar t
  let vu: setvar u
  let cU: class U


  assert |- ( T e. HrmOp -> 0hop <_op ( T o. T ) )

  proof
    cT
    cho
    wcel
    #
    ch0o
    cT
    cT
    ccom
    #
    cleo
    wbr
    #
    cc0
    vx
    cv
    #
    @1
    cfv
    #
    @3
    csp
    co
    #
    cle
    wbr
    #
    vx
    chil
    wral
    #
    @0
    @6
    vx
    chil
    @0
    @3
    chil
    wcel
    #
    wa
    #
    cc0
    @3
    cT
    cfv
    #
    @10
    csp
    co
    #
    @5
    cle
    @9
    @10
    chil
    wcel
    #
    cc0
    @11
    cle
    wbr
    @0
    chil
    chil
    @3
    cT
    cT
    hmopf
    #
    ffvelrnda
    #
    @10
    hiidge0
    syl
    @9
    @11
    @10
    cT
    cfv
    #
    @3
    csp
    co
    #
    @5
    @9
    @0
    @12
    @8
    @11
    @16
    wceq
    @0
    @8
    simpl
    @14
    @0
    @8
    simpr
    @10
    @3
    cT
    hmop
    syl3anc
    @9
    @4
    @15
    @3
    csp
    @0
    chil
    chil
    cT
    wf
    @8
    @4
    @15
    wceq
    @13
    chil
    chil
    @3
    cT
    cT
    fvco3
    sylan
    oveq1d
    eqtr4d
    breqtrd
    ralrimiva
    @0
    @1
    cho
    wcel
    #
    @2
    @7
    wb
    @0
    @17
    @0
    @0
    @1
    @1
    wceq
    @17
    @1
    eqid
    cT
    cT
    hmopco
    mp3an3
    anidms
    vx
    @1
    leoppos
    syl
    mpbird
end
