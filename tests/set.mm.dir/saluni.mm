include "csalg.mm"
include "wcel.mm"
include "cuni.mm"
include "c0.mm"
include "cdif.mm"
include "dif0.mm"
include "0sal.mm"
include "saldifcl.mm"
include "mpdan.mm"
include "syl5eqelr.mm"

theorem saluni
  let cS: class S
  let vk: setvar k
  let vx: setvar x


  assert |- ( S e. SAlg -> U. S e. S )

  proof
    cS
    csalg
    wcel
    #
    cS
    cuni
    #
    @1
    c0
    cdif
    #
    cS
    @1
    dif0
    @0
    c0
    cS
    wcel
    @2
    cS
    wcel
    cS
    0sal
    cS
    c0
    saldifcl
    mpdan
    syl5eqelr
end
