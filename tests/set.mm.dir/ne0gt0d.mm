include "cc0.mm"
include "wne.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wb.mm"
include "ne0gt0.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem ne0gt0d
  let wph: wff ph
  let cA: class A
  assume ltd.1: |- ( ph -> A e. RR )
  assume ne0gt0d.2: |- ( ph -> 0 <_ A )
  assume ne0gt0d.3: |- ( ph -> A =/= 0 )


  assert |- ( ph -> 0 < A )

  proof
    wph
    cA
    cc0
    wne
    #
    cc0
    cA
    clt
    wbr
    #
    ne0gt0d.3
    wph
    cA
    cr
    wcel
    cc0
    cA
    cle
    wbr
    @0
    @1
    wb
    ltd.1
    ne0gt0d.2
    cA
    ne0gt0
    syl2anc
    mpbid
end
