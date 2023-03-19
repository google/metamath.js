include "cr.mm"
include "wcel.mm"
include "ce.mm"
include "cfv.mm"
include "cn0.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cfa.mm"
include "cdiv.mm"
include "csu.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "efval.mm"
include "syl.mm"
include "cmpt.mm"
include "cc0.mm"
include "nn0uz.mm"
include "0zd.mm"
include "eqid.mm"
include "eftval.mm"
include "adantl.mm"
include "reeftcl.mm"
include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "efcllem.mm"
include "isumrecl.mm"
include "eqeltrd.mm"

theorem reefcl
  let cA: class A
  let vk: setvar k
  let vn: setvar n


  assert |- ( A e. RR -> ( exp ` A ) e. RR )

  proof
    cA
    cr
    wcel
    #
    cA
    ce
    cfv
    #
    cn0
    cA
    vk
    cv
    #
    cexp
    co
    @2
    cfa
    cfv
    cdiv
    co
    #
    vk
    csu
    #
    cr
    @0
    cA
    cc
    wcel
    #
    @1
    @4
    wceq
    cA
    recn
    #
    cA
    vk
    efval
    syl
    @0
    @3
    vk
    vn
    cn0
    cA
    vn
    cv
    #
    cexp
    co
    @7
    cfa
    cfv
    cdiv
    co
    cmpt
    #
    cc0
    cn0
    nn0uz
    @0
    0zd
    @2
    cn0
    wcel
    @2
    @8
    cfv
    @3
    wceq
    @0
    cA
    vn
    @8
    @2
    @8
    eqid
    #
    eftval
    adantl
    cA
    @2
    reeftcl
    @0
    @5
    caddc
    @8
    cc0
    cseq
    cli
    cdm
    wcel
    @6
    cA
    vn
    @8
    @9
    efcllem
    syl
    isumrecl
    eqeltrd
end
