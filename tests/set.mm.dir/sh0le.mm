include "csh.mm"
include "wcel.mm"
include "c0h.mm"
include "c0v.mm"
include "csn.mm"
include "df-ch0.mm"
include "sh0.mm"
include "snssd.mm"
include "syl5eqss.mm"

theorem sh0le
  let cA: class A


  assert |- ( A e. SH -> 0H C_ A )

  proof
    cA
    csh
    wcel
    #
    c0h
    c0v
    csn
    cA
    df-ch0
    @0
    c0v
    cA
    cA
    sh0
    snssd
    syl5eqss
end
