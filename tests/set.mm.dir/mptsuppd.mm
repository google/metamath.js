include "csupp.mm"
include "co.mm"
include "cvv.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "crab.mm"
include "wne.mm"
include "mptsuppdifd.mm"
include "cv.mm"
include "wa.mm"
include "elex.mm"
include "syl.mm"
include "biantrurd.mm"
include "eldifsn.mm"
include "syl6rbbr.mm"
include "rabbidva.mm"
include "eqtrd.mm"

theorem mptsuppd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cU: class U
  let cF: class F
  let cV: class V
  let cW: class W
  let cZ: class Z
  assume mptsuppdifd.f: |- F = ( x e. A |-> B )
  assume mptsuppdifd.a: |- ( ph -> A e. V )
  assume mptsuppdifd.z: |- ( ph -> Z e. W )
  assume mptsuppd.b: |- ( ( ph /\ x e. A ) -> B e. U )

  disjoint A x
  disjoint Z x
  disjoint ph x
  assert |- ( ph -> ( F supp Z ) = { x e. A | B =/= Z } )

  proof
    wph
    cF
    cZ
    csupp
    co
    cB
    cvv
    cZ
    csn
    cdif
    wcel
    #
    vx
    cA
    crab
    cB
    cZ
    wne
    #
    vx
    cA
    crab
    wph
    vx
    cA
    cB
    cF
    cV
    cW
    cZ
    mptsuppdifd.f
    mptsuppdifd.a
    mptsuppdifd.z
    mptsuppdifd
    wph
    @0
    @1
    vx
    cA
    wph
    vx
    cv
    cA
    wcel
    wa
    #
    @1
    cB
    cvv
    wcel
    #
    @1
    wa
    @0
    @2
    @3
    @1
    @2
    cB
    cU
    wcel
    @3
    mptsuppd.b
    cB
    cU
    elex
    syl
    biantrurd
    cB
    cvv
    cZ
    eldifsn
    syl6rbbr
    rabbidva
    eqtrd
end
