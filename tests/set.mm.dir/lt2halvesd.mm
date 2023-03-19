include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "lt2halves.mm"
include "syl3anc.mm"
include "mp2and.mm"

theorem lt2halvesd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume rehalfcld.1: |- ( ph -> A e. RR )
  assume lt2halvesd.2: |- ( ph -> B e. RR )
  assume lt2halvesd.3: |- ( ph -> C e. RR )
  assume lt2halvesd.4: |- ( ph -> A < ( C / 2 ) )
  assume lt2halvesd.5: |- ( ph -> B < ( C / 2 ) )


  assert |- ( ph -> ( A + B ) < C )

  proof
    wph
    cA
    cC
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    cB
    @0
    clt
    wbr
    #
    cA
    cB
    caddc
    co
    cC
    clt
    wbr
    #
    lt2halvesd.4
    lt2halvesd.5
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    cC
    cr
    wcel
    @1
    @2
    wa
    @3
    wi
    rehalfcld.1
    lt2halvesd.2
    lt2halvesd.3
    cA
    cB
    cC
    lt2halves
    syl3anc
    mp2and
end
