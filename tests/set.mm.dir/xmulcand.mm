include "cxmu.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "c1.mm"
include "wi.mm"
include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wrex.mm"
include "xrecex.mm"
include "syl2anc.mm"
include "wa.mm"
include "oveq2.mm"
include "cxr.mm"
include "simprl.mm"
include "rexrd.mm"
include "adantr.mm"
include "xmulcom.mm"
include "simprr.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "xmulass.mm"
include "syl3anc.mm"
include "xmulid2.mm"
include "syl.mm"
include "3eqtr3d.mm"
include "eqeq12d.mm"
include "syl5ib.mm"
include "rexlimddv.mm"
include "impbid1.mm"

theorem xmulcand
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  assume xmulcand.1: |- ( ph -> A e. RR* )
  assume xmulcand.2: |- ( ph -> B e. RR* )
  assume xmulcand.3: |- ( ph -> C e. RR )
  assume xmulcand.4: |- ( ph -> C =/= 0 )


  assert |- ( ph -> ( ( C *e A ) = ( C *e B ) <-> A = B ) )

  proof
    wph
    cC
    cA
    cxmu
    co
    #
    cC
    cB
    cxmu
    co
    #
    wceq
    #
    cA
    cB
    wceq
    #
    wph
    cC
    vx
    cv
    #
    cxmu
    co
    #
    c1
    wceq
    #
    @2
    @3
    wi
    vx
    cr
    wph
    cC
    cr
    wcel
    #
    cC
    cc0
    wne
    @6
    vx
    cr
    wrex
    xmulcand.3
    xmulcand.4
    vx
    cC
    xrecex
    syl2anc
    @2
    @4
    @0
    cxmu
    co
    #
    @4
    @1
    cxmu
    co
    #
    wceq
    wph
    @4
    cr
    wcel
    #
    @6
    wa
    #
    wa
    #
    @3
    @0
    @1
    @4
    cxmu
    oveq2
    @12
    @8
    cA
    @9
    cB
    @12
    @4
    cC
    cxmu
    co
    #
    cA
    cxmu
    co
    #
    c1
    cA
    cxmu
    co
    #
    @8
    cA
    @12
    @13
    c1
    cA
    cxmu
    @12
    @13
    @5
    c1
    @12
    @4
    cxr
    wcel
    #
    cC
    cxr
    wcel
    #
    @13
    @5
    wceq
    @12
    @4
    wph
    @10
    @6
    simprl
    rexrd
    #
    @12
    cC
    wph
    @7
    @11
    xmulcand.3
    adantr
    rexrd
    #
    @4
    cC
    xmulcom
    syl2anc
    wph
    @10
    @6
    simprr
    eqtrd
    #
    oveq1d
    @12
    @16
    @17
    cA
    cxr
    wcel
    #
    @14
    @8
    wceq
    @18
    @19
    wph
    @21
    @11
    xmulcand.1
    adantr
    #
    @4
    cC
    cA
    xmulass
    syl3anc
    @12
    @21
    @15
    cA
    wceq
    @22
    cA
    xmulid2
    syl
    3eqtr3d
    @12
    @13
    cB
    cxmu
    co
    #
    c1
    cB
    cxmu
    co
    #
    @9
    cB
    @12
    @13
    c1
    cB
    cxmu
    @20
    oveq1d
    @12
    @16
    @17
    cB
    cxr
    wcel
    #
    @23
    @9
    wceq
    @18
    @19
    wph
    @25
    @11
    xmulcand.2
    adantr
    #
    @4
    cC
    cB
    xmulass
    syl3anc
    @12
    @25
    @24
    cB
    wceq
    @26
    cB
    xmulid2
    syl
    3eqtr3d
    eqeq12d
    syl5ib
    rexlimddv
    cA
    cB
    cC
    cxmu
    oveq2
    impbid1
end
