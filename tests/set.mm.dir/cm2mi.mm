include "cin.mm"
include "ccm.mm"
include "wbr.mm"
include "cort.mm"
include "cfv.mm"
include "chj.mm"
include "co.mm"
include "choccli.mm"
include "cmcm2ii.mm"
include "cm2ji.mm"
include "chdmm1i.mm"
include "breqtrri.mm"
include "chincli.mm"
include "cmcm2i.mm"
include "mpbir.mm"

theorem cm2mi
  let cA: class A
  let cB: class B
  let cC: class C
  assume fh1.1: |- A e. CH
  assume fh1.2: |- B e. CH
  assume fh1.3: |- C e. CH
  assume fh1.4: |- A C_H B
  assume fh1.5: |- A C_H C


  assert |- A C_H ( B i^i C )

  proof
    cA
    cB
    cC
    cin
    #
    ccm
    wbr
    cA
    @0
    cort
    cfv
    #
    ccm
    wbr
    cA
    cB
    cort
    cfv
    #
    cC
    cort
    cfv
    #
    chj
    co
    @1
    ccm
    cA
    @2
    @3
    fh1.1
    cB
    fh1.2
    choccli
    cC
    fh1.3
    choccli
    cA
    cB
    fh1.1
    fh1.2
    fh1.4
    cmcm2ii
    cA
    cC
    fh1.1
    fh1.3
    fh1.5
    cmcm2ii
    cm2ji
    cB
    cC
    fh1.2
    fh1.3
    chdmm1i
    breqtrri
    cA
    @0
    fh1.1
    cB
    cC
    fh1.2
    fh1.3
    chincli
    cmcm2i
    mpbir
end
