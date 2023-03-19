include "cr.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "cneg.mm"
include "cioo.mm"
include "co.mm"
include "elioore.mm"
include "syl.mm"
include "wa.mm"
include "eliooord.mm"
include "1red.mm"
include "absltd.mm"
include "mpbird.mm"
include "jca.mm"

theorem knoppndvlem3
  let wph: wff ph
  let cC: class C
  assume knoppndvlem3.c: |- ( ph -> C e. ( -u 1 (,) 1 ) )


  assert |- ( ph -> ( C e. RR /\ ( abs ` C ) < 1 ) )

  proof
    wph
    cC
    cr
    wcel
    #
    cC
    cabs
    cfv
    c1
    clt
    wbr
    #
    wph
    cC
    c1
    cneg
    #
    c1
    cioo
    co
    wcel
    #
    @0
    knoppndvlem3.c
    cC
    @2
    c1
    elioore
    syl
    #
    wph
    @1
    @2
    cC
    clt
    wbr
    cC
    c1
    clt
    wbr
    wa
    #
    wph
    @3
    @5
    knoppndvlem3.c
    cC
    @2
    c1
    eliooord
    syl
    wph
    cC
    c1
    @4
    wph
    1red
    absltd
    mpbird
    jca
end
