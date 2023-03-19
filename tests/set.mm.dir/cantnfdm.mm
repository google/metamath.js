include "ccnf.mm"
include "co.mm"
include "cdm.mm"
include "cv.mm"
include "c0.mm"
include "csupp.mm"
include "cep.mm"
include "coi.mm"
include "cvv.mm"
include "cfv.mm"
include "coe.mm"
include "comu.mm"
include "coa.mm"
include "cmpt2.mm"
include "cseqom.mm"
include "csb.mm"
include "cmpt.mm"
include "cantnffval.mm"
include "dmeqd.mm"
include "wcel.mm"
include "wral.mm"
include "wceq.mm"
include "fvex.mm"
include "csbex.mm"
include "rgenw.mm"
include "dmmptg.mm"
include "ax-mp.mm"
include "syl6eq.mm"

theorem cantnfdm
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let vg: setvar g
  let vf: setvar f
  let vh: setvar h
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume cantnffval.s: |- S = { g e. ( A ^m B ) | g finSupp (/) }
  assume cantnffval.a: |- ( ph -> A e. On )
  assume cantnffval.b: |- ( ph -> B e. On )

  disjoint A g
  disjoint B g
  disjoint f g
  disjoint f h
  disjoint f k
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g h
  disjoint g k
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint h k
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint A h
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B f
  disjoint B h
  disjoint B k
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint S f
  disjoint S x
  disjoint S y
  assert |- ( ph -> dom ( A CNF B ) = S )

  proof
    wph
    cA
    cB
    ccnf
    co
    #
    cdm
    vf
    cS
    vh
    vf
    cv
    #
    c0
    csupp
    co
    cep
    coi
    #
    vh
    cv
    #
    cdm
    #
    vk
    vz
    cvv
    cvv
    cA
    vk
    cv
    @3
    cfv
    #
    coe
    co
    @5
    @1
    cfv
    comu
    co
    vz
    cv
    coa
    co
    cmpt2
    c0
    cseqom
    #
    cfv
    #
    csb
    #
    cmpt
    #
    cdm
    #
    cS
    wph
    @0
    @9
    wph
    vz
    cA
    cB
    cS
    vf
    vg
    vh
    vk
    cantnffval.s
    cantnffval.a
    cantnffval.b
    cantnffval
    dmeqd
    @8
    cvv
    wcel
    #
    vf
    cS
    wral
    @10
    cS
    wceq
    @11
    vf
    cS
    vh
    @2
    @7
    @4
    @6
    fvex
    csbex
    rgenw
    vf
    cS
    @8
    cvv
    dmmptg
    ax-mp
    syl6eq
end
