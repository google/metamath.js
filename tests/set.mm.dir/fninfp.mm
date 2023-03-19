include "wfn.mm"
include "cid.mm"
include "cin.mm"
include "cdm.mm"
include "cres.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "crab.mm"
include "inres.mm"
include "incom.mm"
include "reseq1i.mm"
include "eqtri.mm"
include "3eqtr4i.mm"
include "fnresdm.mm"
include "ineq1d.mm"
include "syl5reqr.mm"
include "dmeqd.mm"
include "fnresi.mm"
include "fndmin.mm"
include "mpan2.mm"
include "wcel.mm"
include "fvresi.mm"
include "eqeq2d.mm"
include "rabbiia.mm"
include "a1i.mm"
include "3eqtrd.mm"

theorem fninfp
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cX: class X

  disjoint F x
  disjoint A x
  disjoint X x
  assert |- ( F Fn A -> dom ( F i^i _I ) = { x e. A | ( F ` x ) = x } )

  proof
    cF
    cA
    wfn
    #
    cF
    cid
    cin
    #
    cdm
    cF
    cid
    cA
    cres
    #
    cin
    #
    cdm
    #
    vx
    cv
    #
    cF
    cfv
    #
    @5
    @2
    cfv
    #
    wceq
    #
    vx
    cA
    crab
    #
    @6
    @5
    wceq
    #
    vx
    cA
    crab
    #
    @0
    @1
    @3
    @0
    @3
    cF
    cA
    cres
    #
    cid
    cin
    #
    @1
    cid
    @12
    cin
    #
    @1
    cA
    cres
    #
    @13
    @3
    @14
    cid
    cF
    cin
    #
    cA
    cres
    @15
    cid
    cF
    cA
    inres
    @16
    @1
    cA
    cid
    cF
    incom
    reseq1i
    eqtri
    @12
    cid
    incom
    cF
    cid
    cA
    inres
    3eqtr4i
    @0
    @12
    cF
    cid
    cA
    cF
    fnresdm
    ineq1d
    syl5reqr
    dmeqd
    @0
    @2
    cA
    wfn
    @4
    @9
    wceq
    cA
    fnresi
    vx
    cA
    cF
    @2
    fndmin
    mpan2
    @9
    @11
    wceq
    @0
    @8
    @10
    vx
    cA
    @5
    cA
    wcel
    @7
    @5
    @6
    cA
    @5
    fvresi
    eqeq2d
    rabbiia
    a1i
    3eqtrd
end
