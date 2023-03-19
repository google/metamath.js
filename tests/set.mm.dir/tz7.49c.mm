include "wcel.mm"
include "cv.mm"
include "cima.mm"
include "cdif.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "wi.mm"
include "con0.mm"
include "wral.mm"
include "wa.mm"
include "wceq.mm"
include "cres.mm"
include "ccnv.mm"
include "wfun.mm"
include "w3a.mm"
include "wrex.mm"
include "wf1o.mm"
include "biid.mm"
include "tz7.49.mm"
include "3simpc.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "onss.mm"
include "fnssres.mm"
include "sylancr.mm"
include "df-ima.mm"
include "eqeq1i.mm"
include "biimpi.mm"
include "anim12i.mm"
include "anim1i.mm"
include "dff1o2.mm"
include "3anan32.mm"
include "bitri.mm"
include "sylibr.mm"
include "expl.mm"
include "syl5.mm"
include "reximia.mm"
include "syl.mm"

theorem tz7.49c
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vy: setvar y
  assume tz7.49c.1: |- F Fn On

  disjoint A x
  disjoint F x
  disjoint A y
  disjoint x y
  disjoint F y
  assert |- ( ( A e. B /\ A. x e. On ( ( A \ ( F " x ) ) =/= (/) -> ( F ` x ) e. ( A \ ( F " x ) ) ) ) -> E. x e. On ( F |` x ) : x -1-1-onto-> A )

  proof
    cA
    cB
    wcel
    cA
    cF
    vx
    cv
    #
    cima
    #
    cdif
    #
    c0
    wne
    @0
    cF
    cfv
    @2
    wcel
    wi
    vx
    con0
    wral
    #
    wa
    cA
    cF
    vy
    cv
    cima
    cdif
    c0
    wne
    vy
    @0
    wral
    #
    @1
    cA
    wceq
    #
    cF
    @0
    cres
    #
    ccnv
    wfun
    #
    w3a
    #
    vx
    con0
    wrex
    @0
    cA
    @6
    wf1o
    #
    vx
    con0
    wrex
    @3
    vx
    vy
    cA
    cB
    cF
    tz7.49c.1
    @3
    biid
    tz7.49
    @8
    @9
    vx
    con0
    @8
    @5
    @7
    wa
    @0
    con0
    wcel
    #
    @9
    @4
    @5
    @7
    3simpc
    @10
    @5
    @7
    @9
    @10
    @5
    wa
    #
    @7
    wa
    @6
    @0
    wfn
    #
    @6
    crn
    #
    cA
    wceq
    #
    wa
    #
    @7
    wa
    #
    @9
    @11
    @15
    @7
    @10
    @12
    @5
    @14
    @10
    cF
    con0
    wfn
    @0
    con0
    wss
    @12
    tz7.49c.1
    @0
    onss
    con0
    @0
    cF
    fnssres
    sylancr
    @5
    @14
    @1
    @13
    cA
    cF
    @0
    df-ima
    eqeq1i
    biimpi
    anim12i
    anim1i
    @9
    @12
    @7
    @14
    w3a
    @16
    @0
    cA
    @6
    dff1o2
    @12
    @7
    @14
    3anan32
    bitri
    sylibr
    expl
    syl5
    reximia
    syl
end
