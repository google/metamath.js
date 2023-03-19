include "caddc.mm"
include "co.mm"
include "c3.mm"
include "cmul.mm"
include "c4.mm"
include "clt.mm"
include "readdcld.mm"
include "cr.mm"
include "wcel.mm"
include "3re.mm"
include "a1i.mm"
include "remulcld.mm"
include "lt3addmuld.mm"
include "lt2addd.mm"
include "c1.mm"
include "wceq.mm"
include "df-4.mm"
include "oveq1d.mm"
include "recnd.mm"
include "adddirp1d.mm"
include "eqtr2d.mm"
include "breqtrd.mm"

theorem lt4addmuld
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  assume lt4addmuld.a: |- ( ph -> A e. RR )
  assume lt4addmuld.b: |- ( ph -> B e. RR )
  assume lt4addmuld.c: |- ( ph -> C e. RR )
  assume lt4addmuld.d: |- ( ph -> D e. RR )
  assume lt4addmuld.e: |- ( ph -> E e. RR )
  assume lt4addmuld.alte: |- ( ph -> A < E )
  assume lt4addmuld.blte: |- ( ph -> B < E )
  assume lt4addmuld.clte: |- ( ph -> C < E )
  assume lt4addmuld.dlte: |- ( ph -> D < E )


  assert |- ( ph -> ( ( ( A + B ) + C ) + D ) < ( 4 x. E ) )

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
    #
    cD
    caddc
    co
    c3
    cE
    cmul
    co
    #
    cE
    caddc
    co
    #
    c4
    cE
    cmul
    co
    #
    clt
    wph
    @1
    cD
    @2
    cE
    wph
    @0
    cC
    wph
    cA
    cB
    lt4addmuld.a
    lt4addmuld.b
    readdcld
    lt4addmuld.c
    readdcld
    lt4addmuld.d
    wph
    c3
    cE
    c3
    cr
    wcel
    wph
    3re
    a1i
    #
    lt4addmuld.e
    remulcld
    lt4addmuld.e
    wph
    cA
    cB
    cC
    cE
    lt4addmuld.a
    lt4addmuld.b
    lt4addmuld.c
    lt4addmuld.e
    lt4addmuld.alte
    lt4addmuld.blte
    lt4addmuld.clte
    lt3addmuld
    lt4addmuld.dlte
    lt2addd
    wph
    @4
    c3
    c1
    caddc
    co
    #
    cE
    cmul
    co
    @3
    wph
    c4
    @6
    cE
    cmul
    c4
    @6
    wceq
    wph
    df-4
    a1i
    oveq1d
    wph
    c3
    cE
    wph
    c3
    @5
    recnd
    wph
    cE
    lt4addmuld.e
    recnd
    adddirp1d
    eqtr2d
    breqtrd
end
