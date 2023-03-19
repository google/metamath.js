include "cn0.mm"
include "wcel.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "w3a.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "wa.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "anim12i.mm"
include "3adant1.mm"
include "eqfnfv2.mm"
include "syl.mm"
include "cuz.mm"
include "elnn0uz.mm"
include "fzopth.mm"
include "sylbi.mm"
include "simpr.mm"
include "syl6bi.mm"
include "anim1d.mm"
include "oveq2.mm"
include "anim1i.mm"
include "impbid1.mm"
include "3ad2ant1.mm"
include "bitrd.mm"

theorem 2ffzeq
  let cP: class P
  let vi: setvar i
  let cF: class F
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y

  disjoint F i
  disjoint M i
  disjoint P i
  assert |- ( ( M e. NN0 /\ F : ( 0 ... M ) --> X /\ P : ( 0 ... N ) --> Y ) -> ( F = P <-> ( M = N /\ A. i e. ( 0 ... M ) ( F ` i ) = ( P ` i ) ) ) )

  proof
    cM
    cn0
    wcel
    #
    cc0
    cM
    cfz
    co
    #
    cX
    cF
    wf
    #
    cc0
    cN
    cfz
    co
    #
    cY
    cP
    wf
    #
    w3a
    #
    cF
    cP
    wceq
    #
    @1
    @3
    wceq
    #
    vi
    cv
    #
    cF
    cfv
    @8
    cP
    cfv
    wceq
    vi
    @1
    wral
    #
    wa
    #
    cM
    cN
    wceq
    #
    @9
    wa
    #
    @5
    cF
    @1
    wfn
    #
    cP
    @3
    wfn
    #
    wa
    #
    @6
    @10
    wb
    @2
    @4
    @15
    @0
    @2
    @13
    @4
    @14
    @1
    cX
    cF
    ffn
    @3
    cY
    cP
    ffn
    anim12i
    3adant1
    vi
    @1
    @3
    cF
    cP
    eqfnfv2
    syl
    @0
    @2
    @10
    @12
    wb
    @4
    @0
    @10
    @12
    @0
    @7
    @11
    @9
    @0
    @7
    cc0
    cc0
    wceq
    #
    @11
    wa
    #
    @11
    @0
    cM
    cc0
    cuz
    cfv
    wcel
    @7
    @17
    wb
    cM
    elnn0uz
    cc0
    cN
    cc0
    cM
    fzopth
    sylbi
    @16
    @11
    simpr
    syl6bi
    anim1d
    @11
    @7
    @9
    cM
    cN
    cc0
    cfz
    oveq2
    anim1i
    impbid1
    3ad2ant1
    bitrd
end
