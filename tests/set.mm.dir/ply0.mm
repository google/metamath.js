include "cc.mm"
include "wss.mm"
include "c0p.mm"
include "cc0.mm"
include "csn.mm"
include "cun.mm"
include "cply.mm"
include "cfv.mm"
include "cxp.mm"
include "df-0p.mm"
include "wcel.mm"
include "id.mm"
include "0cnd.mm"
include "snssd.mm"
include "unssd.mm"
include "ssun2.mm"
include "c0ex.mm"
include "snss.mm"
include "mpbir.mm"
include "plyconst.mm"
include "sylancl.mm"
include "syl5eqel.mm"
include "plyun0.mm"
include "syl6eleq.mm"

theorem ply0
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


  assert |- ( S C_ CC -> 0p e. ( Poly ` S ) )

  proof
    cS
    cc
    wss
    #
    c0p
    cS
    cc0
    csn
    #
    cun
    #
    cply
    cfv
    #
    cS
    cply
    cfv
    @0
    c0p
    cc
    @1
    cxp
    #
    @3
    df-0p
    @0
    @2
    cc
    wss
    cc0
    @2
    wcel
    #
    @4
    @3
    wcel
    @0
    cS
    @1
    cc
    @0
    id
    @0
    cc0
    cc
    @0
    0cnd
    snssd
    unssd
    @5
    @1
    @2
    wss
    @1
    cS
    ssun2
    cc0
    @2
    c0ex
    snss
    mpbir
    cc0
    @2
    plyconst
    sylancl
    syl5eqel
    cS
    plyun0
    syl6eleq
end
