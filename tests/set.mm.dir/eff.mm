include "cc.mm"
include "cn0.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cfa.mm"
include "cfv.mm"
include "cdiv.mm"
include "csu.mm"
include "ce.mm"
include "df-ef.mm"
include "wcel.mm"
include "cmpt.mm"
include "cc0.mm"
include "nn0uz.mm"
include "0zd.mm"
include "wceq.mm"
include "eqid.mm"
include "eftval.mm"
include "adantl.mm"
include "eftcl.mm"
include "efcllem.mm"
include "isumcl.mm"
include "fmpti.mm"

theorem eff
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x


  assert |- exp : CC --> CC

  proof
    vx
    cc
    cc
    cn0
    vx
    cv
    #
    vk
    cv
    #
    cexp
    co
    @1
    cfa
    cfv
    cdiv
    co
    #
    vk
    csu
    ce
    vx
    vk
    df-ef
    @0
    cc
    wcel
    #
    @2
    vk
    vn
    cn0
    @0
    vn
    cv
    #
    cexp
    co
    @4
    cfa
    cfv
    cdiv
    co
    cmpt
    #
    cc0
    cn0
    nn0uz
    @3
    0zd
    @1
    cn0
    wcel
    @1
    @5
    cfv
    @2
    wceq
    @3
    @0
    vn
    @5
    @1
    @5
    eqid
    #
    eftval
    adantl
    @0
    @1
    eftcl
    @0
    vn
    @5
    @6
    efcllem
    isumcl
    fmpti
end
