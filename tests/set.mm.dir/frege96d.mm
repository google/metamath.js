include "ctcl.mm"
include "cfv.mm"
include "ccom.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "brcogw.mm"
include "syl32anc.mm"
include "wss.mm"
include "trclfvlb.mm"
include "coss1.mm"
include "3syl.mm"
include "trclfvcotrg.mm"
include "syl6ss.mm"
include "ssbrd.mm"
include "mpd.mm"

theorem frege96d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume frege96d.r: |- ( ph -> R e. _V )
  assume frege96d.a: |- ( ph -> A e. _V )
  assume frege96d.b: |- ( ph -> B e. _V )
  assume frege96d.c: |- ( ph -> C e. _V )
  assume frege96d.ac: |- ( ph -> A ( t+ ` R ) C )
  assume frege96d.cb: |- ( ph -> C R B )


  assert |- ( ph -> A ( t+ ` R ) B )

  proof
    wph
    cA
    cB
    cR
    cR
    ctcl
    cfv
    #
    ccom
    #
    wbr
    #
    cA
    cB
    @0
    wbr
    wph
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    cC
    cvv
    wcel
    cA
    cC
    @0
    wbr
    cC
    cB
    cR
    wbr
    @2
    frege96d.a
    frege96d.b
    frege96d.c
    frege96d.ac
    frege96d.cb
    cA
    cB
    cR
    @0
    cvv
    cvv
    cC
    cvv
    brcogw
    syl32anc
    wph
    @1
    @0
    cA
    cB
    wph
    @1
    @0
    @0
    ccom
    #
    @0
    wph
    cR
    cvv
    wcel
    cR
    @0
    wss
    @1
    @3
    wss
    frege96d.r
    cR
    cvv
    trclfvlb
    cR
    @0
    @0
    coss1
    3syl
    cR
    trclfvcotrg
    syl6ss
    ssbrd
    mpd
end
