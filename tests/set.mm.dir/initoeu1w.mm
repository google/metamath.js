include "ccic.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "ciso.mm"
include "co.mm"
include "wcel.mm"
include "wex.mm"
include "weu.mm"
include "initoeu1.mm"
include "euex.mm"
include "syl.mm"
include "cbs.mm"
include "eqid.mm"
include "ccat.mm"
include "cinito.mm"
include "initoo.mm"
include "sylc.mm"
include "cic.mm"
include "mpbird.mm"

theorem initoeu1w
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let va: setvar a
  let vg: setvar g
  let vb: setvar b
  let vf: setvar f
  assume initoeu1.c: |- ( ph -> C e. Cat )
  assume initoeu1.a: |- ( ph -> A e. ( InitO ` C ) )
  assume initoeu1.b: |- ( ph -> B e. ( InitO ` C ) )


  assert |- ( ph -> A ( ~=c ` C ) B )

  proof
    wph
    cA
    cB
    cC
    ccic
    cfv
    wbr
    vf
    cv
    cA
    cB
    cC
    ciso
    cfv
    #
    co
    wcel
    #
    vf
    wex
    #
    wph
    @1
    vf
    weu
    @2
    wph
    cA
    cB
    cC
    vf
    initoeu1.c
    initoeu1.a
    initoeu1.b
    initoeu1
    @1
    vf
    euex
    syl
    wph
    cC
    cbs
    cfv
    #
    cC
    vf
    @0
    cA
    cB
    @0
    eqid
    @3
    eqid
    initoeu1.c
    wph
    cC
    ccat
    wcel
    #
    cA
    cC
    cinito
    cfv
    #
    wcel
    cA
    @3
    wcel
    initoeu1.c
    initoeu1.a
    cC
    cA
    initoo
    sylc
    wph
    @4
    cB
    @5
    wcel
    cB
    @3
    wcel
    initoeu1.c
    initoeu1.b
    cC
    cB
    initoo
    sylc
    cic
    mpbird
end
