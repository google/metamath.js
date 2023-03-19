include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "caddc.mm"
include "cc0.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "efcllem.mm"
include "adantr.mm"
include "nn0uz.mm"
include "simpr.mm"
include "cv.mm"
include "cfv.mm"
include "cexp.mm"
include "co.mm"
include "cfa.mm"
include "cdiv.mm"
include "wceq.mm"
include "eftval.mm"
include "adantl.mm"
include "eftcl.mm"
include "adantlr.mm"
include "eqeltrd.mm"
include "iserex.mm"
include "mpbid.mm"

theorem eftlcvg
  let cA: class A
  let vn: setvar n
  let cF: class F
  let cM: class M
  let vj: setvar j
  let vk: setvar k
  let cG: class G
  let cH: class H
  let wph: wff ph
  assume eftl.1: |- F = ( n e. NN0 |-> ( ( A ^ n ) / ( ! ` n ) ) )

  disjoint A n
  disjoint M n
  disjoint j k
  disjoint j n
  disjoint A j
  disjoint k n
  disjoint A k
  disjoint F k
  disjoint G j
  disjoint G k
  disjoint H j
  disjoint M j
  disjoint M k
  disjoint j ph
  disjoint k ph
  assert |- ( ( A e. CC /\ M e. NN0 ) -> seq M ( + , F ) e. dom ~~> )

  proof
    cA
    cc
    wcel
    #
    cM
    cn0
    wcel
    #
    wa
    #
    caddc
    cF
    cc0
    cseq
    cli
    cdm
    #
    wcel
    #
    caddc
    cF
    cM
    cseq
    @3
    wcel
    @0
    @4
    @1
    cA
    vn
    cF
    eftl.1
    efcllem
    adantr
    @2
    vk
    cF
    cc0
    cM
    cn0
    nn0uz
    @0
    @1
    simpr
    @2
    vk
    cv
    #
    cn0
    wcel
    #
    wa
    @5
    cF
    cfv
    #
    cA
    @5
    cexp
    co
    @5
    cfa
    cfv
    cdiv
    co
    #
    cc
    @6
    @7
    @8
    wceq
    @2
    cA
    vn
    cF
    @5
    eftl.1
    eftval
    adantl
    @0
    @6
    @8
    cc
    wcel
    @1
    cA
    @5
    eftcl
    adantlr
    eqeltrd
    iserex
    mpbid
end
