include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wn.mm"
include "wa.mm"
include "jca.mm"
include "cr.mm"
include "wcel.mm"
include "wb.mm"
include "eqlelt.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem lenlteq
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume lenlteq.1: |- ( ph -> A e. RR )
  assume lenlteq.2: |- ( ph -> B e. RR )
  assume lenlteq.3: |- ( ph -> A <_ B )
  assume lenlteq.4: |- ( ph -> -. A < B )


  assert |- ( ph -> A = B )

  proof
    wph
    cA
    cB
    wceq
    #
    cA
    cB
    cle
    wbr
    #
    cA
    cB
    clt
    wbr
    wn
    #
    wa
    #
    wph
    @1
    @2
    lenlteq.3
    lenlteq.4
    jca
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    @0
    @3
    wb
    lenlteq.1
    lenlteq.2
    cA
    cB
    eqlelt
    syl2anc
    mpbird
end
