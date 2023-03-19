include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cle.mm"
include "rehalfcld.mm"
include "le2addd.mm"
include "recnd.mm"
include "2halvesd.mm"
include "breqtrd.mm"

theorem le2halvesd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume le2halvesd.1: |- ( ph -> A e. RR )
  assume le2halvesd.2: |- ( ph -> B e. RR )
  assume le2halvesd.3: |- ( ph -> C e. RR )
  assume le2halvesd.4: |- ( ph -> A <_ ( C / 2 ) )
  assume le2halvesd.5: |- ( ph -> B <_ ( C / 2 ) )


  assert |- ( ph -> ( A + B ) <_ C )

  proof
    wph
    cA
    cB
    caddc
    co
    cC
    c2
    cdiv
    co
    #
    @0
    caddc
    co
    cC
    cle
    wph
    cA
    cB
    @0
    @0
    le2halvesd.1
    le2halvesd.2
    wph
    cC
    le2halvesd.3
    rehalfcld
    #
    @1
    le2halvesd.4
    le2halvesd.5
    le2addd
    wph
    cC
    wph
    cC
    le2halvesd.3
    recnd
    2halvesd
    breqtrd
end
