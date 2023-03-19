include "wfn.mm"
include "cid.mm"
include "cdif.mm"
include "cdm.mm"
include "cres.mm"
include "cv.mm"
include "cfv.mm"
include "wne.mm"
include "crab.mm"
include "cvv.mm"
include "cxp.mm"
include "cun.mm"
include "c0.mm"
include "wss.mm"
include "wceq.mm"
include "wf.mm"
include "dffn2.mm"
include "fssxp.mm"
include "sylbi.mm"
include "ssdif0.mm"
include "sylib.mm"
include "uneq2d.mm"
include "un0.mm"
include "syl6req.mm"
include "cin.mm"
include "df-res.mm"
include "difeq2i.mm"
include "difindi.mm"
include "eqtri.mm"
include "syl6eqr.mm"
include "dmeqd.mm"
include "fnresi.mm"
include "fndmdif.mm"
include "mpan2.mm"
include "wcel.mm"
include "fvresi.mm"
include "neeq2d.mm"
include "rabbiia.mm"
include "a1i.mm"
include "3eqtrd.mm"

theorem fndifnfp
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cX: class X

  disjoint F x
  disjoint A x
  disjoint X x
  assert |- ( F Fn A -> dom ( F \ _I ) = { x e. A | ( F ` x ) =/= x } )

  proof
    cF
    cA
    wfn
    #
    cF
    cid
    cdif
    #
    cdm
    cF
    cid
    cA
    cres
    #
    cdif
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
    wne
    #
    vx
    cA
    crab
    #
    @6
    @5
    wne
    #
    vx
    cA
    crab
    #
    @0
    @1
    @3
    @0
    @1
    @1
    cF
    cA
    cvv
    cxp
    #
    cdif
    #
    cun
    #
    @3
    @0
    @14
    @1
    c0
    cun
    @1
    @0
    @13
    c0
    @1
    @0
    cF
    @12
    wss
    #
    @13
    c0
    wceq
    @0
    cA
    cvv
    cF
    wf
    @15
    cA
    cF
    dffn2
    cA
    cvv
    cF
    fssxp
    sylbi
    cF
    @12
    ssdif0
    sylib
    uneq2d
    @1
    un0
    syl6req
    @3
    cF
    cid
    @12
    cin
    #
    cdif
    @14
    @2
    @16
    cF
    cid
    cA
    df-res
    difeq2i
    cF
    cid
    @12
    difindi
    eqtri
    syl6eqr
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
    fndmdif
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
    neeq2d
    rabbiia
    a1i
    3eqtrd
end
