include "cpr.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "cle.mm"
include "wne.mm"
include "wceq.mm"
include "wcel.mm"
include "wb.mm"
include "hashprg.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "wss.mm"
include "wbr.mm"
include "prssd.mm"
include "hashss.mm"
include "eqbrtrrd.mm"

theorem nehash2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cV: class V
  assume nehash2.p: |- ( ph -> P e. V )
  assume nehash2.a: |- ( ph -> A e. P )
  assume nehash2.b: |- ( ph -> B e. P )
  assume nehash2.1: |- ( ph -> A =/= B )


  assert |- ( ph -> 2 <_ ( # ` P ) )

  proof
    wph
    cA
    cB
    cpr
    #
    chash
    cfv
    #
    c2
    cP
    chash
    cfv
    #
    cle
    wph
    cA
    cB
    wne
    #
    @1
    c2
    wceq
    #
    nehash2.1
    wph
    cA
    cP
    wcel
    cB
    cP
    wcel
    @3
    @4
    wb
    nehash2.a
    nehash2.b
    cA
    cB
    cP
    cP
    hashprg
    syl2anc
    mpbid
    wph
    cP
    cV
    wcel
    @0
    cP
    wss
    @1
    @2
    cle
    wbr
    nehash2.p
    wph
    cA
    cB
    cP
    nehash2.a
    nehash2.b
    prssd
    cP
    @0
    cV
    hashss
    syl2anc
    eqbrtrrd
end
