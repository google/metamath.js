include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cmul.mm"
include "clt.mm"
include "lt2addd.mm"
include "recnd.mm"
include "2timesd.mm"
include "breqtrrd.mm"

theorem lt2addmuld
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume lt2addmuld.a: |- ( ph -> A e. RR )
  assume lt2addmuld.b: |- ( ph -> B e. RR )
  assume lt2addmuld.c: |- ( ph -> C e. RR )
  assume lt2addmuld.altc: |- ( ph -> A < C )
  assume lt2addmuld.bltc: |- ( ph -> B < C )


  assert |- ( ph -> ( A + B ) < ( 2 x. C ) )

  proof
    wph
    cA
    cB
    caddc
    co
    cC
    cC
    caddc
    co
    c2
    cC
    cmul
    co
    clt
    wph
    cA
    cB
    cC
    cC
    lt2addmuld.a
    lt2addmuld.b
    lt2addmuld.c
    lt2addmuld.c
    lt2addmuld.altc
    lt2addmuld.bltc
    lt2addd
    wph
    cC
    wph
    cC
    lt2addmuld.c
    recnd
    2timesd
    breqtrrd
end
