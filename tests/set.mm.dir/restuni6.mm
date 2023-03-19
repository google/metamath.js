include "crest.mm"
include "co.mm"
include "cuni.mm"
include "cin.mm"
include "wcel.mm"
include "wceq.mm"
include "eqid.mm"
include "restin.mm"
include "syl2anc.mm"
include "unieqd.mm"
include "wss.mm"
include "inss2.mm"
include "a1i.mm"
include "restuni4.mm"
include "incom.mm"
include "3eqtrd.mm"

theorem restuni6
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  assume restuni6.1: |- ( ph -> A e. V )
  assume restuni6.2: |- ( ph -> B e. W )


  assert |- ( ph -> U. ( A |`t B ) = ( U. A i^i B ) )

  proof
    wph
    cA
    cB
    crest
    co
    #
    cuni
    cA
    cB
    cA
    cuni
    #
    cin
    #
    crest
    co
    #
    cuni
    @2
    @1
    cB
    cin
    #
    wph
    @0
    @3
    wph
    cA
    cV
    wcel
    cB
    cW
    wcel
    @0
    @3
    wceq
    restuni6.1
    restuni6.2
    cB
    cA
    cV
    cW
    @1
    @1
    eqid
    restin
    syl2anc
    unieqd
    wph
    cA
    @2
    cV
    restuni6.1
    @2
    @1
    wss
    wph
    cB
    @1
    inss2
    a1i
    restuni4
    @2
    @4
    wceq
    wph
    cB
    @1
    incom
    a1i
    3eqtrd
end
