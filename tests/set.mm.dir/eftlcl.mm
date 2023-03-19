include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cuz.mm"
include "eqid.mm"
include "cz.mm"
include "nn0z.mm"
include "adantl.mm"
include "eqidd.mm"
include "cexp.mm"
include "co.mm"
include "cfa.mm"
include "cdiv.mm"
include "wceq.mm"
include "eluznn0.mm"
include "adantll.mm"
include "eftval.mm"
include "syl.mm"
include "simpll.mm"
include "eftcl.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "eftlcvg.mm"
include "isumcl.mm"

theorem eftlcl
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cM: class M
  let vj: setvar j
  let cG: class G
  let cH: class H
  let wph: wff ph
  assume eftl.1: |- F = ( n e. NN0 |-> ( ( A ^ n ) / ( ! ` n ) ) )

  disjoint k n
  disjoint A k
  disjoint A n
  disjoint F k
  disjoint M k
  disjoint M n
  disjoint j k
  disjoint j n
  disjoint A j
  disjoint G j
  disjoint G k
  disjoint H j
  disjoint M j
  disjoint j ph
  disjoint k ph
  assert |- ( ( A e. CC /\ M e. NN0 ) -> sum_ k e. ( ZZ>= ` M ) ( F ` k ) e. CC )

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
    vk
    cv
    #
    cF
    cfv
    #
    vk
    cF
    cM
    cM
    cuz
    cfv
    #
    @5
    eqid
    @1
    cM
    cz
    wcel
    @0
    cM
    nn0z
    adantl
    @2
    @3
    @5
    wcel
    #
    wa
    #
    @4
    eqidd
    @7
    @4
    cA
    @3
    cexp
    co
    @3
    cfa
    cfv
    cdiv
    co
    #
    cc
    @7
    @3
    cn0
    wcel
    #
    @4
    @8
    wceq
    @1
    @6
    @9
    @0
    @3
    cM
    eluznn0
    adantll
    #
    cA
    vn
    cF
    @3
    eftl.1
    eftval
    syl
    @7
    @0
    @9
    @8
    cc
    wcel
    @0
    @1
    @6
    simpll
    @10
    cA
    @3
    eftcl
    syl2anc
    eqeltrd
    cA
    vn
    cF
    cM
    eftl.1
    eftlcvg
    isumcl
end
