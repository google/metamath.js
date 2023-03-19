include "wdfat.mm"
include "cdm.mm"
include "wcel.mm"
include "csn.mm"
include "cres.mm"
include "wfun.mm"
include "wa.mm"
include "df-dfat.mm"
include "nfdm.mm"
include "nfel.mm"
include "nfsn.mm"
include "nfres.mm"
include "nffun.mm"
include "nfan.mm"
include "nfxfr.mm"

theorem nfdfat
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vk: setvar k
  assume nfdfat.1: |- F/_ x F
  assume nfdfat.2: |- F/_ x A


  assert |- F/ x F defAt A

  proof
    cA
    cF
    wdfat
    cA
    cF
    cdm
    #
    wcel
    #
    cF
    cA
    csn
    #
    cres
    #
    wfun
    #
    wa
    vx
    cA
    cF
    df-dfat
    @1
    @4
    vx
    vx
    cA
    @0
    nfdfat.2
    vx
    cF
    nfdfat.1
    nfdm
    nfel
    vx
    @3
    vx
    cF
    @2
    nfdfat.1
    vx
    cA
    nfdfat.2
    nfsn
    nfres
    nffun
    nfan
    nfxfr
end
