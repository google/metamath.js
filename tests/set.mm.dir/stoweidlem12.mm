include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cfv.mm"
include "cexp.mm"
include "co.mm"
include "cmin.mm"
include "cr.mm"
include "wceq.mm"
include "simpr.mm"
include "1red.mm"
include "ffvelrnda.mm"
include "cn0.mm"
include "adantr.mm"
include "reexpcld.mm"
include "resubcld.mm"
include "jca.mm"
include "nn0expcl.mm"
include "syl.mm"
include "fvmpt2.mm"
include "syl2anc.mm"

theorem stoweidlem12
  let wph: wff ph
  let vt: setvar t
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cK: class K
  let cN: class N
  let vk: setvar k
  let vx: setvar x
  assume stoweidlem12.1: |- Q = ( t e. T |-> ( ( 1 - ( ( P ` t ) ^ N ) ) ^ ( K ^ N ) ) )
  assume stoweidlem12.2: |- ( ph -> P : T --> RR )
  assume stoweidlem12.3: |- ( ph -> N e. NN0 )
  assume stoweidlem12.4: |- ( ph -> K e. NN0 )

  disjoint T t
  disjoint k x
  assert |- ( ( ph /\ t e. T ) -> ( Q ` t ) = ( ( 1 - ( ( P ` t ) ^ N ) ) ^ ( K ^ N ) ) )

  proof
    wph
    vt
    cv
    #
    cT
    wcel
    #
    wa
    #
    @1
    c1
    @0
    cP
    cfv
    #
    cN
    cexp
    co
    #
    cmin
    co
    #
    cK
    cN
    cexp
    co
    #
    cexp
    co
    #
    cr
    wcel
    @0
    cQ
    cfv
    @7
    wceq
    wph
    @1
    simpr
    @2
    @5
    @6
    @2
    c1
    @4
    @2
    1red
    @2
    @3
    cN
    wph
    cT
    cr
    @0
    cP
    stoweidlem12.2
    ffvelrnda
    wph
    cN
    cn0
    wcel
    #
    @1
    stoweidlem12.3
    adantr
    reexpcld
    resubcld
    @2
    cK
    cn0
    wcel
    #
    @8
    wa
    #
    @6
    cn0
    wcel
    wph
    @10
    @1
    wph
    @9
    @8
    stoweidlem12.4
    stoweidlem12.3
    jca
    adantr
    cK
    cN
    nn0expcl
    syl
    reexpcld
    vt
    cT
    @7
    cr
    cQ
    stoweidlem12.1
    fvmpt2
    syl2anc
end
