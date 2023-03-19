include "cioo.mm"
include "co.mm"
include "cmpt.mm"
include "cibl.mm"
include "wcel.mm"
include "cicc.mm"
include "wb.mm"
include "citg.mm"
include "wceq.mm"
include "wss.mm"
include "ioossicc.mm"
include "a1i.mm"
include "iccssred.mm"
include "cdif.mm"
include "cpr.mm"
include "cr.mm"
include "covol.mm"
include "cfv.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "c0.mm"
include "cxr.mm"
include "rexrd.mm"
include "icc0.mm"
include "syl2anc.mm"
include "biimpar.mm"
include "difeq1d.mm"
include "0dif.mm"
include "0ss.mm"
include "eqsstri.mm"
include "syl6eqss.mm"
include "cle.mm"
include "ssid.mm"
include "adantr.mm"
include "simpr.mm"
include "iccdifioo.mm"
include "syl3anc.mm"
include "syl5sseq.mm"
include "ltlecasei.mm"
include "prssi.mm"
include "cfn.mm"
include "prfi.mm"
include "ovolfi.mm"
include "sylancr.mm"
include "ovolssnul.mm"
include "itgss3.mm"
include "simpld.mm"
include "mpbid.mm"

theorem ibliooicc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  assume ibliooicc.1: |- ( ph -> A e. RR )
  assume ibliooicc.2: |- ( ph -> B e. RR )
  assume ibliooicc.3: |- ( ph -> ( x e. ( A (,) B ) |-> C ) e. L^1 )
  assume ibliooicc.4: |- ( ( ph /\ x e. ( A [,] B ) ) -> C e. CC )

  disjoint A x
  disjoint B x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( x e. ( A [,] B ) |-> C ) e. L^1 )

  proof
    wph
    vx
    cA
    cB
    cioo
    co
    #
    cC
    cmpt
    cibl
    wcel
    #
    vx
    cA
    cB
    cicc
    co
    #
    cC
    cmpt
    cibl
    wcel
    #
    ibliooicc.3
    wph
    @1
    @3
    wb
    vx
    @0
    cC
    citg
    vx
    @2
    cC
    citg
    wceq
    wph
    vx
    @0
    @2
    cC
    @0
    @2
    wss
    wph
    cA
    cB
    ioossicc
    a1i
    wph
    cA
    cB
    ibliooicc.1
    ibliooicc.2
    iccssred
    wph
    @2
    @0
    cdif
    #
    cA
    cB
    cpr
    #
    wss
    #
    @5
    cr
    wss
    #
    @5
    covol
    cfv
    cc0
    wceq
    #
    @4
    covol
    cfv
    cc0
    wceq
    wph
    @6
    cB
    cA
    wph
    cB
    cA
    clt
    wbr
    #
    wa
    #
    @4
    c0
    @0
    cdif
    #
    @5
    @10
    @2
    c0
    @0
    wph
    @2
    c0
    wceq
    #
    @9
    wph
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @12
    @9
    wb
    wph
    cA
    ibliooicc.1
    rexrd
    #
    wph
    cB
    ibliooicc.2
    rexrd
    #
    cA
    cB
    icc0
    syl2anc
    biimpar
    difeq1d
    @11
    c0
    @5
    @0
    0dif
    @5
    0ss
    eqsstri
    syl6eqss
    wph
    cA
    cB
    cle
    wbr
    #
    wa
    #
    @4
    @4
    @5
    @4
    ssid
    @18
    @13
    @14
    @17
    @4
    @5
    wceq
    wph
    @13
    @17
    @15
    adantr
    wph
    @14
    @17
    @16
    adantr
    wph
    @17
    simpr
    cA
    cB
    iccdifioo
    syl3anc
    syl5sseq
    ibliooicc.2
    ibliooicc.1
    ltlecasei
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    @7
    ibliooicc.1
    ibliooicc.2
    cA
    cB
    cr
    prssi
    syl2anc
    #
    wph
    @5
    cfn
    wcel
    @7
    @8
    cA
    cB
    prfi
    @19
    @5
    ovolfi
    sylancr
    @4
    @5
    ovolssnul
    syl3anc
    ibliooicc.4
    itgss3
    simpld
    mpbid
end
