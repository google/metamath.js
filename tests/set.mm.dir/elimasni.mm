include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cima.mm"
include "wbr.mm"
include "wn.mm"
include "c0.mm"
include "noel.mm"
include "wceq.mm"
include "snprc.mm"
include "biimpi.mm"
include "imaeq2d.mm"
include "ima0.mm"
include "syl6eq.mm"
include "eleq2d.mm"
include "mtbiri.mm"
include "con4i.mm"
include "elex.mm"
include "jca.mm"
include "cop.mm"
include "elimasng.mm"
include "df-br.mm"
include "syl6bbr.mm"
include "biimpd.mm"
include "mpcom.mm"

theorem elimasni
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( C e. ( A " { B } ) -> B A C )

  proof
    cB
    cvv
    wcel
    #
    cC
    cvv
    wcel
    #
    wa
    #
    cC
    cA
    cB
    csn
    #
    cima
    #
    wcel
    #
    cB
    cC
    cA
    wbr
    #
    @5
    @0
    @1
    @0
    @5
    @0
    wn
    #
    @5
    cC
    c0
    wcel
    cC
    noel
    @7
    @4
    c0
    cC
    @7
    @4
    cA
    c0
    cima
    c0
    @7
    @3
    c0
    cA
    @7
    @3
    c0
    wceq
    cB
    snprc
    biimpi
    imaeq2d
    cA
    ima0
    syl6eq
    eleq2d
    mtbiri
    con4i
    cC
    @4
    elex
    jca
    @2
    @5
    @6
    @2
    @5
    cB
    cC
    cop
    cA
    wcel
    @6
    cA
    cB
    cC
    cvv
    cvv
    elimasng
    cB
    cC
    cA
    df-br
    syl6bbr
    biimpd
    mpcom
end
