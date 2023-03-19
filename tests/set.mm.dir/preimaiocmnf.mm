include "ccnv.mm"
include "cmnf.mm"
include "cioc.mm"
include "co.mm"
include "cima.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "crab.mm"
include "cle.mm"
include "wbr.mm"
include "wfn.mm"
include "wceq.mm"
include "cr.mm"
include "ffnd.mm"
include "fncnvima2.mm"
include "syl.mm"
include "wa.mm"
include "wi.mm"
include "cxr.mm"
include "mnfxr.mm"
include "a1i.mm"
include "adantr.mm"
include "simpr.mm"
include "iocleubd.mm"
include "ex.mm"
include "adantlr.mm"
include "ffvelrnda.mm"
include "rexrd.mm"
include "clt.mm"
include "mnfltd.mm"
include "eliocd.mm"
include "impbid.mm"
include "rabbidva.mm"
include "eqtrd.mm"

theorem preimaiocmnf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  assume preimaiocmnf.1: |- ( ph -> F : A --> RR )
  assume preimaiocmnf.2: |- ( ph -> B e. RR* )

  disjoint A x
  disjoint B x
  disjoint F x
  disjoint ph x
  assert |- ( ph -> ( `' F " ( -oo (,] B ) ) = { x e. A | ( F ` x ) <_ B } )

  proof
    wph
    cF
    ccnv
    cmnf
    cB
    cioc
    co
    #
    cima
    #
    vx
    cv
    #
    cF
    cfv
    #
    @0
    wcel
    #
    vx
    cA
    crab
    #
    @3
    cB
    cle
    wbr
    #
    vx
    cA
    crab
    wph
    cF
    cA
    wfn
    @1
    @5
    wceq
    wph
    cA
    cr
    cF
    preimaiocmnf.1
    ffnd
    vx
    cA
    @0
    cF
    fncnvima2
    syl
    wph
    @4
    @6
    vx
    cA
    wph
    @2
    cA
    wcel
    #
    wa
    #
    @4
    @6
    wph
    @4
    @6
    wi
    @7
    wph
    @4
    @6
    wph
    @4
    wa
    #
    cmnf
    cB
    @3
    cmnf
    cxr
    wcel
    #
    @9
    mnfxr
    a1i
    wph
    cB
    cxr
    wcel
    #
    @4
    preimaiocmnf.2
    adantr
    wph
    @4
    simpr
    iocleubd
    ex
    adantr
    @8
    @6
    @4
    @8
    @6
    wa
    #
    cmnf
    cB
    @3
    @10
    @12
    mnfxr
    a1i
    wph
    @6
    @11
    @7
    wph
    @11
    @6
    preimaiocmnf.2
    adantr
    adantlr
    @8
    @3
    cxr
    wcel
    @6
    @8
    @3
    wph
    cA
    cr
    @2
    cF
    preimaiocmnf.1
    ffvelrnda
    #
    rexrd
    adantr
    @8
    cmnf
    @3
    clt
    wbr
    @6
    @8
    @3
    @13
    mnfltd
    adantr
    @8
    @6
    simpr
    eliocd
    ex
    impbid
    rabbidva
    eqtrd
end
