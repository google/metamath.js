include "caltop.mm"
include "csn.mm"
include "cpr.mm"
include "df-altop.mm"
include "nfsn.mm"
include "nfpr.mm"
include "nfcxfr.mm"

theorem nfaltop
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume nfaltop.1: |- F/_ x A
  assume nfaltop.2: |- F/_ x B


  assert |- F/_ x << A , B >>

  proof
    vx
    cA
    cB
    caltop
    cA
    csn
    #
    cA
    cB
    csn
    #
    cpr
    #
    cpr
    cA
    cB
    df-altop
    vx
    @0
    @2
    vx
    cA
    nfaltop.1
    nfsn
    vx
    cA
    @1
    nfaltop.1
    vx
    cB
    nfaltop.2
    nfsn
    nfpr
    nfpr
    nfcxfr
end
