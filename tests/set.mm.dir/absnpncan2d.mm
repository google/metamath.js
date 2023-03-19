include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "caddc.mm"
include "subcld.mm"
include "abscld.mm"
include "readdcld.mm"
include "absnpncand.mm"
include "leadd1dd.mm"
include "letrd.mm"

theorem absnpncan2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume absnpncan2d.a: |- ( ph -> A e. CC )
  assume absnpncan2d.b: |- ( ph -> B e. CC )
  assume absnpncan2d.c: |- ( ph -> C e. CC )
  assume absnpncan2d.d: |- ( ph -> D e. CC )


  assert |- ( ph -> ( abs ` ( A - D ) ) <_ ( ( ( abs ` ( A - B ) ) + ( abs ` ( B - C ) ) ) + ( abs ` ( C - D ) ) ) )

  proof
    wph
    cA
    cD
    cmin
    co
    #
    cabs
    cfv
    cA
    cC
    cmin
    co
    #
    cabs
    cfv
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
    @4
    caddc
    co
    wph
    @0
    wph
    cA
    cD
    absnpncan2d.a
    absnpncan2d.d
    subcld
    abscld
    wph
    @2
    @4
    wph
    @1
    wph
    cA
    cC
    absnpncan2d.a
    absnpncan2d.c
    subcld
    abscld
    #
    wph
    @3
    wph
    cC
    cD
    absnpncan2d.c
    absnpncan2d.d
    subcld
    abscld
    #
    readdcld
    wph
    @9
    @4
    wph
    @6
    @8
    wph
    @5
    wph
    cA
    cB
    absnpncan2d.a
    absnpncan2d.b
    subcld
    abscld
    wph
    @7
    wph
    cB
    cC
    absnpncan2d.b
    absnpncan2d.c
    subcld
    abscld
    readdcld
    #
    @11
    readdcld
    wph
    cA
    cC
    cD
    absnpncan2d.a
    absnpncan2d.c
    absnpncan2d.d
    absnpncand
    wph
    @2
    @9
    @4
    @10
    @12
    @11
    wph
    cA
    cB
    cC
    absnpncan2d.a
    absnpncan2d.b
    absnpncan2d.c
    absnpncand
    leadd1dd
    letrd
end
