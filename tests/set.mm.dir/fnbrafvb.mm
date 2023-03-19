include "wfn.mm"
include "wcel.mm"
include "wa.mm"
include "cafv.mm"
include "wceq.mm"
include "cfv.mm"
include "wbr.mm"
include "cdm.mm"
include "csn.mm"
include "cres.mm"
include "wfun.mm"
include "wi.mm"
include "fndm.mm"
include "wb.mm"
include "eleq2.mm"
include "eqcoms.mm"
include "biimpd.mm"
include "syl.mm"
include "imp.mm"
include "wss.mm"
include "snssi.mm"
include "adantl.mm"
include "fnssresb.mm"
include "adantr.mm"
include "mpbird.mm"
include "fnfun.mm"
include "wdfat.mm"
include "df-dfat.mm"
include "afvfundmfveq.mm"
include "sylbir.mm"
include "syl2anc.mm"
include "eqeq1d.mm"
include "fnbrfvb.mm"
include "bitrd.mm"

theorem fnbrafvb
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( F Fn A /\ B e. A ) -> ( ( F ''' B ) = C <-> B F C ) )

  proof
    cF
    cA
    wfn
    #
    cB
    cA
    wcel
    #
    wa
    #
    cB
    cF
    cafv
    #
    cC
    wceq
    cB
    cF
    cfv
    #
    cC
    wceq
    cB
    cC
    cF
    wbr
    @2
    @3
    @4
    cC
    @2
    cB
    cF
    cdm
    #
    wcel
    #
    cF
    cB
    csn
    #
    cres
    #
    wfun
    #
    @3
    @4
    wceq
    #
    @0
    @1
    @6
    @0
    @5
    cA
    wceq
    #
    @1
    @6
    wi
    cA
    cF
    fndm
    @11
    @1
    @6
    @1
    @6
    wb
    cA
    @5
    cA
    @5
    cB
    eleq2
    eqcoms
    biimpd
    syl
    imp
    @2
    @8
    @7
    wfn
    #
    @9
    @2
    @12
    @7
    cA
    wss
    #
    @1
    @13
    @0
    cB
    cA
    snssi
    adantl
    @0
    @12
    @13
    wb
    @1
    cA
    @7
    cF
    fnssresb
    adantr
    mpbird
    @7
    @8
    fnfun
    syl
    @6
    @9
    wa
    cB
    cF
    wdfat
    @10
    cB
    cF
    df-dfat
    cB
    cF
    afvfundmfveq
    sylbir
    syl2anc
    eqeq1d
    cA
    cB
    cC
    cF
    fnbrfvb
    bitrd
end
