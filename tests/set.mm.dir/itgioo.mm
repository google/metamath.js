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
include "cr.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "cdif.mm"
include "cpr.mm"
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
include "biimpar.mm"
include "difeq1d.mm"
include "0dif.mm"
include "0ss.mm"
include "eqsstri.mm"
include "syl6eqss.mm"
include "cle.mm"
include "cun.mm"
include "uncom.mm"
include "adantr.mm"
include "simpr.mm"
include "prunioo.mm"
include "syl3anc.mm"
include "syl5req.mm"
include "difun2.mm"
include "syl6eq.mm"
include "difss.mm"
include "ltlecasei.mm"
include "prssi.mm"
include "cfn.mm"
include "prfi.mm"
include "ovolfi.mm"
include "sylancr.mm"
include "ovolssnul.mm"
include "itgss3.mm"
include "simprd.mm"

theorem itgioo
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume itgioo.1: |- ( ph -> A e. RR )
  assume itgioo.2: |- ( ph -> B e. RR )
  assume itgioo.3: |- ( ( ph /\ x e. ( A [,] B ) ) -> C e. CC )

  disjoint A x
  disjoint B x
  disjoint ph x
  assert |- ( ph -> S. ( A (,) B ) C _d x = S. ( A [,] B ) C _d x )

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
    wb
    vx
    @0
    cC
    citg
    vx
    @1
    cC
    citg
    wceq
    wph
    vx
    @0
    @1
    cC
    @0
    @1
    wss
    wph
    cA
    cB
    ioossicc
    a1i
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @1
    cr
    wss
    itgioo.1
    itgioo.2
    cA
    cB
    iccssre
    syl2anc
    wph
    @1
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
    @1
    c0
    @0
    wph
    @1
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
    itgioo.1
    rexrd
    #
    wph
    cB
    itgioo.2
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
    @5
    @0
    cdif
    #
    @5
    @18
    @4
    @5
    @0
    cun
    #
    @0
    cdif
    @19
    @18
    @1
    @20
    @0
    @18
    @20
    @0
    @5
    cun
    #
    @1
    @5
    @0
    uncom
    @18
    @13
    @14
    @17
    @21
    @1
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
    prunioo
    syl3anc
    syl5req
    difeq1d
    @5
    @0
    difun2
    syl6eq
    @5
    @0
    difss
    syl6eqss
    itgioo.2
    itgioo.1
    ltlecasei
    wph
    @2
    @3
    @7
    itgioo.1
    itgioo.2
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
    @22
    @5
    ovolfi
    sylancr
    @4
    @5
    ovolssnul
    syl3anc
    itgioo.3
    itgss3
    simprd
end
