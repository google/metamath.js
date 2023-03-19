include "cc.mm"
include "wss.mm"
include "c1.mm"
include "wcel.mm"
include "wa.mm"
include "cidp.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cmpt.mm"
include "cply.mm"
include "cfv.mm"
include "cid.mm"
include "cres.mm"
include "mptresid.mm"
include "exp1.mm"
include "mpteq2ia.mm"
include "df-idp.mm"
include "3eqtr4ri.mm"
include "cn0.mm"
include "1nn0.mm"
include "plypow.mm"
include "mp3an3.mm"
include "syl5eqel.mm"

theorem plyid
  let cS: class S
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cM: class M
  let cN: class N
  let wph: wff ph


  assert |- ( ( S C_ CC /\ 1 e. S ) -> Xp e. ( Poly ` S ) )

  proof
    cS
    cc
    wss
    #
    c1
    cS
    wcel
    #
    wa
    cidp
    vz
    cc
    vz
    cv
    #
    c1
    cexp
    co
    #
    cmpt
    #
    cS
    cply
    cfv
    #
    vz
    cc
    @2
    cmpt
    cid
    cc
    cres
    @4
    cidp
    vz
    cc
    mptresid
    vz
    cc
    @3
    @2
    @2
    exp1
    mpteq2ia
    df-idp
    3eqtr4ri
    @0
    @1
    c1
    cn0
    wcel
    @4
    @5
    wcel
    1nn0
    vz
    cS
    c1
    plypow
    mp3an3
    syl5eqel
end
