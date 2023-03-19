include "cn.mm"
include "wcel.mm"
include "cmu.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "cprime.mm"
include "cpc.mm"
include "co.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "wral.mm"
include "wi.mm"
include "issqf.mm"
include "biimpa.mm"
include "wceq.mm"
include "oveq1.mm"
include "breq1d.mm"
include "rspccv.mm"
include "syl.mm"
include "3impia.mm"

theorem sqfpc
  let cA: class A
  let cP: class P
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cK: class K
  let cM: class M
  let cN: class N
  let cS: class S
  let cB: class B


  assert |- ( ( A e. NN /\ ( mmu ` A ) =/= 0 /\ P e. Prime ) -> ( P pCnt A ) <_ 1 )

  proof
    cA
    cn
    wcel
    #
    cA
    cmu
    cfv
    cc0
    wne
    #
    cP
    cprime
    wcel
    #
    cP
    cA
    cpc
    co
    #
    c1
    cle
    wbr
    #
    @0
    @1
    wa
    vp
    cv
    #
    cA
    cpc
    co
    #
    c1
    cle
    wbr
    #
    vp
    cprime
    wral
    #
    @2
    @4
    wi
    @0
    @1
    @8
    cA
    vp
    issqf
    biimpa
    @7
    @4
    vp
    cP
    cprime
    @5
    cP
    wceq
    @6
    @3
    c1
    cle
    @5
    cP
    cA
    cpc
    oveq1
    breq1d
    rspccv
    syl
    3impia
end
