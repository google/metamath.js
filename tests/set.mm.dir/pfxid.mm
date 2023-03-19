include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "cpfx.mm"
include "co.mm"
include "cc0.mm"
include "cop.mm"
include "csubstr.mm"
include "cn0.mm"
include "wceq.mm"
include "lencl.mm"
include "pfxval.mm"
include "mpdan.mm"
include "swrdid.mm"
include "eqtrd.mm"

theorem pfxid
  let cA: class A
  let cS: class S
  let vk: setvar k
  let vx: setvar x


  assert |- ( S e. Word A -> ( S prefix ( # ` S ) ) = S )

  proof
    cS
    cA
    cword
    #
    wcel
    #
    cS
    cS
    chash
    cfv
    #
    cpfx
    co
    #
    cS
    cc0
    @2
    cop
    csubstr
    co
    #
    cS
    @1
    @2
    cn0
    wcel
    @3
    @4
    wceq
    cA
    cS
    lencl
    cS
    @2
    @0
    pfxval
    mpdan
    cA
    cS
    swrdid
    eqtrd
end
