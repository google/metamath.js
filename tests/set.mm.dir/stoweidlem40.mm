include "cv.mm"
include "cfv.mm"
include "cexp.mm"
include "co.mm"
include "cmpt.mm"
include "c1.mm"
include "cmin.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "wceq.mm"
include "simpr.mm"
include "1red.mm"
include "ffvelrnda.mm"
include "cn0.mm"
include "nnnn0d.mm"
include "adantr.mm"
include "reexpcld.mm"
include "resubcld.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "mpteq2da.mm"
include "syl5eq.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "1re.mm"
include "mpan2.mm"
include "adantl.mm"
include "oveq12d.mm"
include "stoweidlem4.mm"
include "syl5eqel.mm"
include "stoweidlem19.mm"
include "stoweidlem33.mm"
include "mpd3an23.mm"
include "eqeltrd.mm"

theorem stoweidlem40
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cN: class N
  let vk: setvar k
  assume stoweidlem40.1: |- F/_ t P
  assume stoweidlem40.2: |- F/ t ph
  assume stoweidlem40.3: |- Q = ( t e. T |-> ( ( 1 - ( ( P ` t ) ^ N ) ) ^ M ) )
  assume stoweidlem40.4: |- F = ( t e. T |-> ( 1 - ( ( P ` t ) ^ N ) ) )
  assume stoweidlem40.5: |- G = ( t e. T |-> 1 )
  assume stoweidlem40.6: |- H = ( t e. T |-> ( ( P ` t ) ^ N ) )
  assume stoweidlem40.7: |- ( ph -> P e. A )
  assume stoweidlem40.8: |- ( ph -> P : T --> RR )
  assume stoweidlem40.9: |- ( ( ph /\ f e. A ) -> f : T --> RR )
  assume stoweidlem40.10: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) + ( g ` t ) ) ) e. A )
  assume stoweidlem40.11: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) e. A )
  assume stoweidlem40.12: |- ( ( ph /\ x e. RR ) -> ( t e. T |-> x ) e. A )
  assume stoweidlem40.13: |- ( ph -> N e. NN )
  assume stoweidlem40.14: |- ( ph -> M e. NN )

  disjoint f g
  disjoint f t
  disjoint A f
  disjoint g t
  disjoint A g
  disjoint A t
  disjoint F f
  disjoint F g
  disjoint G f
  disjoint G g
  disjoint H f
  disjoint H g
  disjoint P f
  disjoint P g
  disjoint T f
  disjoint T g
  disjoint T t
  disjoint f ph
  disjoint g ph
  disjoint t x
  disjoint A x
  disjoint M t
  disjoint N t
  disjoint T x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> Q e. A )

  proof
    wph
    cQ
    vt
    cT
    vt
    cv
    #
    cF
    cfv
    #
    cM
    cexp
    co
    #
    cmpt
    #
    cA
    wph
    cQ
    vt
    cT
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
    cM
    cexp
    co
    #
    cmpt
    @3
    stoweidlem40.3
    wph
    vt
    cT
    @7
    @2
    stoweidlem40.2
    wph
    @0
    cT
    wcel
    #
    wa
    #
    @6
    @1
    cM
    cexp
    @9
    @1
    @6
    @9
    @8
    @6
    cr
    wcel
    @1
    @6
    wceq
    wph
    @8
    simpr
    #
    @9
    c1
    @5
    @9
    1red
    @9
    @4
    cN
    wph
    cT
    cr
    @0
    cP
    stoweidlem40.8
    ffvelrnda
    wph
    cN
    cn0
    wcel
    @8
    wph
    cN
    stoweidlem40.13
    nnnn0d
    #
    adantr
    reexpcld
    #
    resubcld
    vt
    cT
    @6
    cr
    cF
    stoweidlem40.4
    fvmpt2
    syl2anc
    eqcomd
    oveq1d
    mpteq2da
    syl5eq
    wph
    vx
    vt
    cA
    cT
    vf
    vg
    cF
    cM
    vt
    cF
    vt
    cT
    @6
    cmpt
    #
    stoweidlem40.4
    vt
    cT
    @6
    nfmpt1
    nfcxfr
    stoweidlem40.2
    stoweidlem40.9
    stoweidlem40.11
    stoweidlem40.12
    wph
    cF
    vt
    cT
    @0
    cG
    cfv
    #
    @0
    cH
    cfv
    #
    cmin
    co
    #
    cmpt
    #
    cA
    wph
    cF
    @13
    @17
    stoweidlem40.4
    wph
    vt
    cT
    @6
    @16
    stoweidlem40.2
    @9
    c1
    @14
    @5
    @15
    cmin
    @8
    c1
    @14
    wceq
    wph
    @8
    @14
    c1
    @8
    c1
    cr
    wcel
    #
    @14
    c1
    wceq
    1re
    vt
    cT
    c1
    cr
    cG
    stoweidlem40.5
    fvmpt2
    mpan2
    eqcomd
    adantl
    @9
    @15
    @5
    @9
    @8
    @5
    cr
    wcel
    @15
    @5
    wceq
    @10
    @12
    vt
    cT
    @5
    cr
    cH
    stoweidlem40.6
    fvmpt2
    syl2anc
    eqcomd
    oveq12d
    mpteq2da
    syl5eq
    wph
    cG
    cA
    wcel
    cH
    cA
    wcel
    @17
    cA
    wcel
    wph
    cG
    vt
    cT
    c1
    cmpt
    #
    cA
    stoweidlem40.5
    wph
    @18
    @19
    cA
    wcel
    1re
    wph
    vx
    vt
    cA
    c1
    cT
    stoweidlem40.12
    stoweidlem4
    mpan2
    syl5eqel
    wph
    cH
    vt
    cT
    @5
    cmpt
    #
    cA
    stoweidlem40.6
    wph
    vx
    vt
    cA
    cT
    vf
    vg
    cP
    cN
    stoweidlem40.1
    stoweidlem40.2
    stoweidlem40.9
    stoweidlem40.11
    stoweidlem40.12
    stoweidlem40.7
    @11
    stoweidlem19
    syl5eqel
    wph
    vx
    vt
    cA
    cT
    vf
    vg
    cG
    cH
    vt
    cG
    @19
    stoweidlem40.5
    vt
    cT
    c1
    nfmpt1
    nfcxfr
    vt
    cH
    @20
    stoweidlem40.6
    vt
    cT
    @5
    nfmpt1
    nfcxfr
    stoweidlem40.2
    stoweidlem40.9
    stoweidlem40.10
    stoweidlem40.11
    stoweidlem40.12
    stoweidlem33
    mpd3an23
    eqeltrd
    wph
    cM
    stoweidlem40.14
    nnnn0d
    stoweidlem19
    eqeltrd
end
