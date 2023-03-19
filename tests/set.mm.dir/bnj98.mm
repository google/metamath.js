include "cv.mm"
include "csuc.mm"
include "c1o.mm"
include "wcel.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "wceq.mm"
include "wi.mm"
include "com.mm"
include "c0.mm"
include "vex.mm"
include "sucid.mm"
include "n0ii.mm"
include "csn.mm"
include "wo.mm"
include "cab.mm"
include "cun.mm"
include "df-suc.mm"
include "df-un.mm"
include "eqtri.mm"
include "df1o2.mm"
include "eleq12i.mm"
include "elsni.mm"
include "sylbi.mm"
include "syl5eq.mm"
include "mto.mm"
include "pm2.21i.mm"
include "rgenw.mm"

theorem bnj98
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vi: setvar i
  let cF: class F
  let vx: setvar x


  assert |- A. i e. _om ( suc i e. 1o -> ( F ` suc i ) = U_ y e. ( F ` i ) _pred ( y , A , R ) )

  proof
    vi
    cv
    #
    csuc
    #
    c1o
    wcel
    #
    @1
    cF
    cfv
    vy
    @0
    cF
    cfv
    cA
    cR
    vy
    cv
    c-bnj14
    ciun
    wceq
    #
    wi
    vi
    com
    @2
    @3
    @2
    @1
    c0
    wceq
    @0
    @1
    @0
    vi
    vex
    sucid
    n0ii
    @2
    @1
    vx
    cv
    #
    @0
    wcel
    @4
    @0
    csn
    #
    wcel
    wo
    vx
    cab
    #
    c0
    @1
    @0
    @5
    cun
    @6
    @0
    df-suc
    vx
    @0
    @5
    df-un
    eqtri
    #
    @2
    @6
    c0
    csn
    #
    wcel
    @6
    c0
    wceq
    @1
    @6
    c1o
    @8
    @7
    df1o2
    eleq12i
    @6
    c0
    elsni
    sylbi
    syl5eq
    mto
    pm2.21i
    rgenw
end
