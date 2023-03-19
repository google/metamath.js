include "cho.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cneg.mm"
include "chot.mm"
include "co.mm"
include "chos.mm"
include "chod.mm"
include "chil.mm"
include "wf.mm"
include "wceq.mm"
include "hmopf.mm"
include "honegsub.mm"
include "syl2an.mm"
include "cr.mm"
include "neg1rr.mm"
include "hmopm.mm"
include "mpan.mm"
include "hmops.mm"
include "sylan2.mm"
include "eqeltrrd.mm"

theorem hmopd
  let cT: class T
  let cU: class U
  let vx: setvar x
  let vy: setvar y
  let cA: class A


  assert |- ( ( T e. HrmOp /\ U e. HrmOp ) -> ( T -op U ) e. HrmOp )

  proof
    cT
    cho
    wcel
    #
    cU
    cho
    wcel
    #
    wa
    cT
    c1
    cneg
    #
    cU
    chot
    co
    #
    chos
    co
    #
    cT
    cU
    chod
    co
    #
    cho
    @0
    chil
    chil
    cT
    wf
    chil
    chil
    cU
    wf
    @4
    @5
    wceq
    @1
    cT
    hmopf
    cU
    hmopf
    cT
    cU
    honegsub
    syl2an
    @1
    @0
    @3
    cho
    wcel
    #
    @4
    cho
    wcel
    @2
    cr
    wcel
    @1
    @6
    neg1rr
    @2
    cU
    hmopm
    mpan
    cT
    @3
    hmops
    sylan2
    eqeltrrd
end
