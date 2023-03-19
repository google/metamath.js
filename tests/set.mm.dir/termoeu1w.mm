include "ccic.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "ciso.mm"
include "co.mm"
include "wcel.mm"
include "wex.mm"
include "weu.mm"
include "termoeu1.mm"
include "euex.mm"
include "syl.mm"
include "cbs.mm"
include "eqid.mm"
include "ccat.mm"
include "ctermo.mm"
include "termoo.mm"
include "sylc.mm"
include "cic.mm"
include "mpbird.mm"

theorem termoeu1w
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let va: setvar a
  let vg: setvar g
  let vb: setvar b
  let vf: setvar f
  assume termoeu1.c: |- ( ph -> C e. Cat )
  assume termoeu1.a: |- ( ph -> A e. ( TermO ` C ) )
  assume termoeu1.b: |- ( ph -> B e. ( TermO ` C ) )


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
    termoeu1.c
    termoeu1.a
    termoeu1.b
    termoeu1
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
    termoeu1.c
    wph
    cC
    ccat
    wcel
    #
    cA
    cC
    ctermo
    cfv
    #
    wcel
    cA
    @3
    wcel
    termoeu1.c
    termoeu1.a
    cC
    cA
    termoo
    sylc
    wph
    @4
    cB
    @5
    wcel
    cB
    @3
    wcel
    termoeu1.c
    termoeu1.b
    cC
    cB
    termoo
    sylc
    cic
    mpbird
end
