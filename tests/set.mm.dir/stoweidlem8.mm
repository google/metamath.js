include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "cmpt.mm"
include "simp3.mm"
include "wi.mm"
include "wceq.mm"
include "eleq1.mm"
include "3anbi3d.mm"
include "nfeq2.mm"
include "fveq1.mm"
include "oveq2d.mm"
include "adantr.mm"
include "mpteq2da.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "simp2.mm"
include "3anbi2d.mm"
include "oveq1d.mm"
include "vtoclg.mm"
include "mpcom.mm"

theorem stoweidlem8
  let wph: wff ph
  let vt: setvar t
  let cA: class A
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let cG: class G
  let vk: setvar k
  let vx: setvar x
  assume stoweidlem8.1: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) + ( g ` t ) ) ) e. A )
  assume stoweidlem8.2: |- F/_ t F
  assume stoweidlem8.3: |- F/_ t G

  disjoint f g
  disjoint f t
  disjoint g t
  disjoint A f
  disjoint A g
  disjoint F f
  disjoint F g
  disjoint T f
  disjoint T g
  disjoint f ph
  disjoint g ph
  disjoint G g
  disjoint k x
  assert |- ( ( ph /\ F e. A /\ G e. A ) -> ( t e. T |-> ( ( F ` t ) + ( G ` t ) ) ) e. A )

  proof
    cG
    cA
    wcel
    #
    wph
    cF
    cA
    wcel
    #
    @0
    w3a
    #
    vt
    cT
    vt
    cv
    #
    cF
    cfv
    #
    @3
    cG
    cfv
    #
    caddc
    co
    #
    cmpt
    #
    cA
    wcel
    #
    wph
    @1
    @0
    simp3
    wph
    @1
    vg
    cv
    #
    cA
    wcel
    #
    w3a
    #
    vt
    cT
    @4
    @3
    @9
    cfv
    #
    caddc
    co
    #
    cmpt
    #
    cA
    wcel
    #
    wi
    #
    @2
    @8
    wi
    vg
    cG
    cA
    @9
    cG
    wceq
    #
    @11
    @2
    @15
    @8
    @17
    @10
    @0
    wph
    @1
    @9
    cG
    cA
    eleq1
    3anbi3d
    @17
    @14
    @7
    cA
    @17
    vt
    cT
    @13
    @6
    vt
    @9
    cG
    stoweidlem8.3
    nfeq2
    @17
    @13
    @6
    wceq
    @3
    cT
    wcel
    #
    @17
    @12
    @5
    @4
    caddc
    @3
    @9
    cG
    fveq1
    oveq2d
    adantr
    mpteq2da
    eleq1d
    imbi12d
    @1
    @11
    @15
    wph
    @1
    @10
    simp2
    wph
    vf
    cv
    #
    cA
    wcel
    #
    @10
    w3a
    #
    vt
    cT
    @3
    @19
    cfv
    #
    @12
    caddc
    co
    #
    cmpt
    #
    cA
    wcel
    #
    wi
    @16
    vf
    cF
    cA
    @19
    cF
    wceq
    #
    @21
    @11
    @25
    @15
    @26
    @20
    @1
    wph
    @10
    @19
    cF
    cA
    eleq1
    3anbi2d
    @26
    @24
    @14
    cA
    @26
    vt
    cT
    @23
    @13
    vt
    @19
    cF
    stoweidlem8.2
    nfeq2
    @26
    @23
    @13
    wceq
    @18
    @26
    @22
    @4
    @12
    caddc
    @3
    @19
    cF
    fveq1
    oveq1d
    adantr
    mpteq2da
    eleq1d
    imbi12d
    stoweidlem8.1
    vtoclg
    mpcom
    vtoclg
    mpcom
end
