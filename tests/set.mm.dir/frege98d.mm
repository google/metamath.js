include "ctcl.mm"
include "cfv.mm"
include "ccom.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "brcogw.mm"
include "syl32anc.mm"
include "wss.mm"
include "trclfvcotrg.mm"
include "a1i.mm"
include "ssbrd.mm"
include "mpd.mm"

theorem frege98d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume frege98d.a: |- ( ph -> A e. _V )
  assume frege98d.b: |- ( ph -> B e. _V )
  assume frege98d.c: |- ( ph -> C e. _V )
  assume frege98d.ac: |- ( ph -> A ( t+ ` R ) C )
  assume frege98d.cb: |- ( ph -> C ( t+ ` R ) B )


  assert |- ( ph -> A ( t+ ` R ) B )

  proof
    wph
    cA
    cB
    cR
    ctcl
    cfv
    #
    @0
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
    @0
    wbr
    @2
    frege98d.a
    frege98d.b
    frege98d.c
    frege98d.ac
    frege98d.cb
    cA
    cB
    @0
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
    @1
    @0
    wss
    wph
    cR
    trclfvcotrg
    a1i
    ssbrd
    mpd
end
