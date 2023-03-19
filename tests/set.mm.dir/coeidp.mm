include "c1.mm"
include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "cidp.mm"
include "ccoe.mm"
include "cfv.mm"
include "wceq.mm"
include "cc0.mm"
include "cif.mm"
include "ax-1cn.mm"
include "1nn0.mm"
include "cv.mm"
include "cmpt.mm"
include "cid.mm"
include "cres.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "mptresid.mm"
include "exp1.mm"
include "oveq2d.mm"
include "mulid2.mm"
include "eqtrd.mm"
include "mpteq2ia.mm"
include "df-idp.mm"
include "3eqtr4ri.mm"
include "coe1term.mm"
include "mp3an12.mm"

theorem coeidp
  let cA: class A
  let vk: setvar k
  let vz: setvar z
  let cF: class F
  let cN: class N
  let cS: class S


  assert |- ( A e. NN0 -> ( ( coeff ` Xp ) ` A ) = if ( A = 1 , 1 , 0 ) )

  proof
    c1
    cc
    wcel
    c1
    cn0
    wcel
    cA
    cn0
    wcel
    cA
    cidp
    ccoe
    cfv
    cfv
    cA
    c1
    wceq
    c1
    cc0
    cif
    wceq
    ax-1cn
    1nn0
    vz
    c1
    cidp
    cA
    c1
    vz
    cc
    vz
    cv
    #
    cmpt
    cid
    cc
    cres
    vz
    cc
    c1
    @0
    c1
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    cidp
    vz
    cc
    mptresid
    vz
    cc
    @2
    @0
    @0
    cc
    wcel
    #
    @2
    c1
    @0
    cmul
    co
    @0
    @3
    @1
    @0
    c1
    cmul
    @0
    exp1
    oveq2d
    @0
    mulid2
    eqtrd
    mpteq2ia
    df-idp
    3eqtr4ri
    coe1term
    mp3an12
end
