include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cmul.mm"
include "c3.mm"
include "clt.mm"
include "readdcld.mm"
include "cr.mm"
include "wcel.mm"
include "2re.mm"
include "a1i.mm"
include "remulcld.mm"
include "lt2addmuld.mm"
include "lt2addd.mm"
include "c1.mm"
include "recnd.mm"
include "adddirp1d.mm"
include "wceq.mm"
include "2p1e3.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "breqtrd.mm"

theorem lt3addmuld
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume lt3addmuld.a: |- ( ph -> A e. RR )
  assume lt3addmuld.b: |- ( ph -> B e. RR )
  assume lt3addmuld.c: |- ( ph -> C e. RR )
  assume lt3addmuld.d: |- ( ph -> D e. RR )
  assume lt3addmuld.altd: |- ( ph -> A < D )
  assume lt3addmuld.bltd: |- ( ph -> B < D )
  assume lt3addmuld.cltd: |- ( ph -> C < D )


  assert |- ( ph -> ( ( A + B ) + C ) < ( 3 x. D ) )

  proof
    wph
    cA
    cB
    caddc
    co
    #
    cC
    caddc
    co
    c2
    cD
    cmul
    co
    #
    cD
    caddc
    co
    #
    c3
    cD
    cmul
    co
    #
    clt
    wph
    @0
    cC
    @1
    cD
    wph
    cA
    cB
    lt3addmuld.a
    lt3addmuld.b
    readdcld
    lt3addmuld.c
    wph
    c2
    cD
    c2
    cr
    wcel
    wph
    2re
    a1i
    #
    lt3addmuld.d
    remulcld
    lt3addmuld.d
    wph
    cA
    cB
    cD
    lt3addmuld.a
    lt3addmuld.b
    lt3addmuld.d
    lt3addmuld.altd
    lt3addmuld.bltd
    lt2addmuld
    lt3addmuld.cltd
    lt2addd
    wph
    c2
    c1
    caddc
    co
    #
    cD
    cmul
    co
    @2
    @3
    wph
    c2
    cD
    wph
    c2
    @4
    recnd
    wph
    cD
    lt3addmuld.d
    recnd
    adddirp1d
    wph
    @5
    c3
    cD
    cmul
    @5
    c3
    wceq
    wph
    2p1e3
    a1i
    oveq1d
    eqtr3d
    breqtrd
end
