include "cch.mm"
include "wcel.mm"
include "w3a.mm"
include "ccm.mm"
include "wbr.mm"
include "wa.mm"
include "chj.mm"
include "co.mm"
include "cin.mm"
include "wceq.mm"
include "3pm3.2i.mm"
include "pm3.2i.mm"
include "fh1.mm"
include "mp2an.mm"

theorem fh1i
  let cA: class A
  let cB: class B
  let cC: class C
  assume fh1.1: |- A e. CH
  assume fh1.2: |- B e. CH
  assume fh1.3: |- C e. CH
  assume fh1.4: |- A C_H B
  assume fh1.5: |- A C_H C


  assert |- ( A i^i ( B vH C ) ) = ( ( A i^i B ) vH ( A i^i C ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    cC
    cch
    wcel
    #
    w3a
    cA
    cB
    ccm
    wbr
    #
    cA
    cC
    ccm
    wbr
    #
    wa
    cA
    cB
    cC
    chj
    co
    cin
    cA
    cB
    cin
    cA
    cC
    cin
    chj
    co
    wceq
    @0
    @1
    @2
    fh1.1
    fh1.2
    fh1.3
    3pm3.2i
    @3
    @4
    fh1.4
    fh1.5
    pm3.2i
    cA
    cB
    cC
    fh1
    mp2an
end
