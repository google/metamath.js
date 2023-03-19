include "crp.mm"
include "wcel.mm"
include "clgam.mm"
include "cfv.mm"
include "ce.mm"
include "cgam.mm"
include "cc.mm"
include "cz.mm"
include "cn.mm"
include "cdif.mm"
include "wceq.mm"
include "rpdmgm.mm"
include "eflgam.mm"
include "syl.mm"
include "relgamcl.mm"
include "rpefcld.mm"
include "eqeltrrd.mm"

theorem rpgamcl
  let cA: class A
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x


  assert |- ( A e. RR+ -> ( _G ` A ) e. RR+ )

  proof
    cA
    crp
    wcel
    #
    cA
    clgam
    cfv
    #
    ce
    cfv
    #
    cA
    cgam
    cfv
    #
    crp
    @0
    cA
    cc
    cz
    cn
    cdif
    cdif
    wcel
    @2
    @3
    wceq
    cA
    rpdmgm
    cA
    eflgam
    syl
    @0
    @1
    cA
    relgamcl
    rpefcld
    eqeltrrd
end
