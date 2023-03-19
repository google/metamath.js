include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "caddc.mm"
include "subcld.mm"
include "abscld.mm"
include "readdcld.mm"
include "absnpncand.mm"
include "absnpncan2d.mm"
include "leadd1dd.mm"
include "letrd.mm"

theorem absnpncan3d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  assume absnpncan3d.a: |- ( ph -> A e. CC )
  assume absnpncan3d.b: |- ( ph -> B e. CC )
  assume absnpncan3d.c: |- ( ph -> C e. CC )
  assume absnpncan3d.d: |- ( ph -> D e. CC )
  assume absnpncan3d.e: |- ( ph -> E e. CC )


  assert |- ( ph -> ( abs ` ( A - E ) ) <_ ( ( ( ( abs ` ( A - B ) ) + ( abs ` ( B - C ) ) ) + ( abs ` ( C - D ) ) ) + ( abs ` ( D - E ) ) ) )

  proof
    wph
    cA
    cE
    cmin
    co
    #
    cabs
    cfv
    cA
    cD
    cmin
    co
    #
    cabs
    cfv
    #
    cD
    cE
    cmin
    co
    #
    cabs
    cfv
    #
    caddc
    co
    cA
    cB
    cmin
    co
    #
    cabs
    cfv
    #
    cB
    cC
    cmin
    co
    #
    cabs
    cfv
    #
    caddc
    co
    #
    cC
    cD
    cmin
    co
    #
    cabs
    cfv
    #
    caddc
    co
    #
    @4
    caddc
    co
    wph
    @0
    wph
    cA
    cE
    absnpncan3d.a
    absnpncan3d.e
    subcld
    abscld
    wph
    @2
    @4
    wph
    @1
    wph
    cA
    cD
    absnpncan3d.a
    absnpncan3d.d
    subcld
    abscld
    #
    wph
    @3
    wph
    cD
    cE
    absnpncan3d.d
    absnpncan3d.e
    subcld
    abscld
    #
    readdcld
    wph
    @12
    @4
    wph
    @9
    @11
    wph
    @6
    @8
    wph
    @5
    wph
    cA
    cB
    absnpncan3d.a
    absnpncan3d.b
    subcld
    abscld
    wph
    @7
    wph
    cB
    cC
    absnpncan3d.b
    absnpncan3d.c
    subcld
    abscld
    readdcld
    wph
    @10
    wph
    cC
    cD
    absnpncan3d.c
    absnpncan3d.d
    subcld
    abscld
    readdcld
    #
    @14
    readdcld
    wph
    cA
    cD
    cE
    absnpncan3d.a
    absnpncan3d.d
    absnpncan3d.e
    absnpncand
    wph
    @2
    @12
    @4
    @13
    @15
    @14
    wph
    cA
    cB
    cC
    cD
    absnpncan3d.a
    absnpncan3d.b
    absnpncan3d.c
    absnpncan3d.d
    absnpncan2d
    leadd1dd
    letrd
end
