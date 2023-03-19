include "c0.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "c1.mm"
include "cmpt.mm"
include "wceq.mm"
include "mpteq1.mm"
include "mpt0.mm"
include "syl6eq.mm"
include "syl.mm"
include "eqeltrrd.mm"
include "rzal.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"

theorem stoweidlem9
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cT: class T
  let vg: setvar g
  let cE: class E
  let cF: class F
  let vk: setvar k
  let vx: setvar x
  assume stoweidlem9.1: |- ( ph -> T = (/) )
  assume stoweidlem9.2: |- ( ph -> ( t e. T |-> 1 ) e. A )

  disjoint A g
  disjoint E g
  disjoint F g
  disjoint g t
  disjoint T g
  disjoint T t
  disjoint k x
  assert |- ( ph -> E. g e. A A. t e. T ( abs ` ( ( g ` t ) - ( F ` t ) ) ) < E )

  proof
    wph
    c0
    cA
    wcel
    vt
    cv
    #
    c0
    cfv
    #
    @0
    cF
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cE
    clt
    wbr
    #
    vt
    cT
    wral
    #
    @0
    vg
    cv
    #
    cfv
    #
    @2
    cmin
    co
    #
    cabs
    cfv
    #
    cE
    clt
    wbr
    #
    vt
    cT
    wral
    #
    vg
    cA
    wrex
    wph
    vt
    cT
    c1
    cmpt
    #
    c0
    cA
    wph
    cT
    c0
    wceq
    #
    @13
    c0
    wceq
    stoweidlem9.1
    @14
    @13
    vt
    c0
    c1
    cmpt
    c0
    vt
    cT
    c0
    c1
    mpteq1
    vt
    c1
    mpt0
    syl6eq
    syl
    stoweidlem9.2
    eqeltrrd
    wph
    @14
    @6
    stoweidlem9.1
    @5
    vt
    cT
    rzal
    syl
    @12
    @6
    vg
    c0
    cA
    @7
    c0
    wceq
    #
    @11
    @5
    vt
    cT
    @15
    @10
    @4
    cE
    clt
    @15
    @9
    @3
    cabs
    @15
    @8
    @1
    @2
    cmin
    @0
    @7
    c0
    fveq1
    oveq1d
    fveq2d
    breq1d
    ralbidv
    rspcev
    syl2anc
end
