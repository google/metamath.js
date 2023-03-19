include "cnpi.mm"
include "wcel.mm"
include "com.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "elni.mm"
include "word.mm"
include "wb.mm"
include "nnord.mm"
include "ord0eln0.mm"
include "syl.mm"
include "pm5.32i.mm"
include "bitr4i.mm"

theorem elni2
  let cA: class A


  assert |- ( A e. N. <-> ( A e. _om /\ (/) e. A ) )

  proof
    cA
    cnpi
    wcel
    cA
    com
    wcel
    #
    cA
    c0
    wne
    #
    wa
    @0
    c0
    cA
    wcel
    #
    wa
    cA
    elni
    @0
    @2
    @1
    @0
    cA
    word
    @2
    @1
    wb
    cA
    nnord
    cA
    ord0eln0
    syl
    pm5.32i
    bitr4i
end
