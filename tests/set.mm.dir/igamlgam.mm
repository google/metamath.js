include "cc.mm"
include "cz.mm"
include "cn.mm"
include "cdif.mm"
include "wcel.mm"
include "c1.mm"
include "clgam.mm"
include "cfv.mm"
include "ce.mm"
include "cdiv.mm"
include "co.mm"
include "cgam.mm"
include "cneg.mm"
include "cigam.mm"
include "eflgam.mm"
include "oveq2d.mm"
include "wceq.mm"
include "lgamcl.mm"
include "efneg.mm"
include "syl.mm"
include "igamgam.mm"
include "3eqtr4rd.mm"

theorem igamlgam
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x


  assert |- ( A e. ( CC \ ( ZZ \ NN ) ) -> ( 1/_G ` A ) = ( exp ` -u ( log_G ` A ) ) )

  proof
    cA
    cc
    cz
    cn
    cdif
    cdif
    wcel
    #
    c1
    cA
    clgam
    cfv
    #
    ce
    cfv
    #
    cdiv
    co
    #
    c1
    cA
    cgam
    cfv
    #
    cdiv
    co
    @1
    cneg
    ce
    cfv
    #
    cA
    cigam
    cfv
    @0
    @2
    @4
    c1
    cdiv
    cA
    eflgam
    oveq2d
    @0
    @1
    cc
    wcel
    @5
    @3
    wceq
    cA
    lgamcl
    @1
    efneg
    syl
    cA
    igamgam
    3eqtr4rd
end
