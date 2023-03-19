include "wcel.mm"
include "cfz.mm"
include "co.mm"
include "csu.mm"
include "wceq.mm"
include "c1.mm"
include "caddc.mm"
include "cuz.mm"
include "cfv.mm"
include "simpld.mm"
include "syl6eleq.mm"
include "peano2uz.mm"
include "syl6eleqr.mm"
include "syl.mm"
include "syl5eqel.mm"
include "oveq2i.mm"
include "sumeq1i.mm"
include "cv.mm"
include "cc.mm"
include "elfzuz.mm"
include "sylan2.mm"
include "eqeq2i.mm"
include "sylbir.mm"
include "fsump1.mm"
include "syl5eq.mm"
include "simprd.mm"
include "oveq1d.mm"
include "3eqtrd.mm"
include "jca.mm"

theorem fsump1i
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let vk: setvar k
  let cK: class K
  let cM: class M
  let cN: class N
  let cZ: class Z
  assume fsump1i.1: |- Z = ( ZZ>= ` M )
  assume fsump1i.2: |- N = ( K + 1 )
  assume fsump1i.3: |- ( k = N -> A = B )
  assume fsump1i.4: |- ( ( ph /\ k e. Z ) -> A e. CC )
  assume fsump1i.5: |- ( ph -> ( K e. Z /\ sum_ k e. ( M ... K ) A = S ) )
  assume fsump1i.6: |- ( ph -> ( S + B ) = T )

  disjoint B k
  disjoint K k
  disjoint M k
  disjoint N k
  disjoint k ph
  assert |- ( ph -> ( N e. Z /\ sum_ k e. ( M ... N ) A = T ) )

  proof
    wph
    cN
    cZ
    wcel
    cM
    cN
    cfz
    co
    #
    cA
    vk
    csu
    #
    cT
    wceq
    wph
    cN
    cK
    c1
    caddc
    co
    #
    cZ
    fsump1i.2
    wph
    cK
    cM
    cuz
    cfv
    #
    wcel
    #
    @2
    cZ
    wcel
    wph
    cK
    cZ
    @3
    wph
    cK
    cZ
    wcel
    #
    cM
    cK
    cfz
    co
    cA
    vk
    csu
    #
    cS
    wceq
    #
    fsump1i.5
    simpld
    fsump1i.1
    syl6eleq
    #
    @4
    @2
    @3
    cZ
    cM
    cK
    peano2uz
    fsump1i.1
    syl6eleqr
    syl
    syl5eqel
    wph
    @1
    @6
    cB
    caddc
    co
    #
    cS
    cB
    caddc
    co
    cT
    wph
    @1
    cM
    @2
    cfz
    co
    #
    cA
    vk
    csu
    @9
    @0
    @10
    cA
    vk
    cN
    @2
    cM
    cfz
    fsump1i.2
    oveq2i
    sumeq1i
    wph
    cA
    cB
    vk
    cM
    cK
    @8
    vk
    cv
    #
    @10
    wcel
    #
    wph
    @11
    cZ
    wcel
    cA
    cc
    wcel
    @12
    @11
    @3
    cZ
    @11
    cM
    @2
    elfzuz
    fsump1i.1
    syl6eleqr
    fsump1i.4
    sylan2
    @11
    @2
    wceq
    @11
    cN
    wceq
    cA
    cB
    wceq
    cN
    @2
    @11
    fsump1i.2
    eqeq2i
    fsump1i.3
    sylbir
    fsump1
    syl5eq
    wph
    @6
    cS
    cB
    caddc
    wph
    @5
    @7
    fsump1i.5
    simprd
    oveq1d
    fsump1i.6
    3eqtrd
    jca
end
