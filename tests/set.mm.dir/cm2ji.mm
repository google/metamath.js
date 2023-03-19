include "cch.mm"
include "wcel.mm"
include "w3a.mm"
include "ccm.mm"
include "wbr.mm"
include "wa.mm"
include "chj.mm"
include "co.mm"
include "3pm3.2i.mm"
include "pm3.2i.mm"
include "cm2j.mm"
include "mp2an.mm"

theorem cm2ji
  let cA: class A
  let cB: class B
  let cC: class C
  assume fh1.1: |- A e. CH
  assume fh1.2: |- B e. CH
  assume fh1.3: |- C e. CH
  assume fh1.4: |- A C_H B
  assume fh1.5: |- A C_H C


  assert |- A C_H ( B vH C )

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
    ccm
    wbr
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
    cm2j
    mp2an
end
