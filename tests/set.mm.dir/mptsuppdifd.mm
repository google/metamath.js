include "csupp.mm"
include "co.mm"
include "ccnv.mm"
include "cvv.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "wcel.mm"
include "crab.mm"
include "wceq.mm"
include "cmpt.mm"
include "mptexg.mm"
include "syl.mm"
include "syl5eqel.mm"
include "suppimacnv.mm"
include "syl2anc.mm"
include "mptpreima.mm"
include "syl6eq.mm"

theorem mptsuppdifd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let cW: class W
  let cZ: class Z
  assume mptsuppdifd.f: |- F = ( x e. A |-> B )
  assume mptsuppdifd.a: |- ( ph -> A e. V )
  assume mptsuppdifd.z: |- ( ph -> Z e. W )

  disjoint A x
  disjoint Z x
  assert |- ( ph -> ( F supp Z ) = { x e. A | B e. ( _V \ { Z } ) } )

  proof
    wph
    cF
    cZ
    csupp
    co
    #
    cF
    ccnv
    cvv
    cZ
    csn
    cdif
    #
    cima
    #
    cB
    @1
    wcel
    vx
    cA
    crab
    wph
    cF
    cvv
    wcel
    cZ
    cW
    wcel
    @0
    @2
    wceq
    wph
    cF
    vx
    cA
    cB
    cmpt
    #
    cvv
    mptsuppdifd.f
    wph
    cA
    cV
    wcel
    @3
    cvv
    wcel
    mptsuppdifd.a
    vx
    cA
    cB
    cV
    mptexg
    syl
    syl5eqel
    mptsuppdifd.z
    cF
    cvv
    cW
    cZ
    suppimacnv
    syl2anc
    vx
    cA
    cB
    @1
    cF
    mptsuppdifd.f
    mptpreima
    syl6eq
end
