include "cle.mm"
include "wbr.mm"
include "cdit.mm"
include "cioo.mm"
include "co.mm"
include "citg.mm"
include "cneg.mm"
include "wceq.mm"
include "wa.mm"
include "biantrurd.mm"
include "letri3d.mm"
include "bitr4d.mm"
include "cc0.mm"
include "ditg0.mm"
include "neg0.mm"
include "eqtr4i.mm"
include "ditgeq2.mm"
include "c0.mm"
include "oveq1.mm"
include "iooid.mm"
include "syl6eq.mm"
include "itgeq1.mm"
include "syl.mm"
include "itg0.mm"
include "negeqd.mm"
include "3eqtr4a.mm"
include "syl6bi.mm"
include "wn.mm"
include "cif.mm"
include "df-ditg.mm"
include "iffalse.mm"
include "syl5eq.mm"
include "pm2.61d1.mm"

theorem ditgneg
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume ditgpos.1: |- ( ph -> A <_ B )
  assume ditgneg.2: |- ( ph -> A e. RR )
  assume ditgneg.3: |- ( ph -> B e. RR )

  disjoint A x
  disjoint B x
  disjoint ph x
  assert |- ( ph -> S_ [ B -> A ] C _d x = -u S. ( A (,) B ) C _d x )

  proof
    wph
    cB
    cA
    cle
    wbr
    #
    vx
    cB
    cA
    cC
    cdit
    #
    vx
    cA
    cB
    cioo
    co
    #
    cC
    citg
    #
    cneg
    #
    wceq
    #
    wph
    @0
    cA
    cB
    wceq
    #
    @5
    wph
    @0
    cA
    cB
    cle
    wbr
    #
    @0
    wa
    @6
    wph
    @7
    @0
    ditgpos.1
    biantrurd
    wph
    cA
    cB
    ditgneg.2
    ditgneg.3
    letri3d
    bitr4d
    @6
    vx
    cB
    cB
    cC
    cdit
    #
    cc0
    cneg
    #
    @1
    @4
    @8
    cc0
    @9
    vx
    cB
    cC
    ditg0
    neg0
    eqtr4i
    vx
    cA
    cB
    cB
    cC
    ditgeq2
    @6
    @3
    cc0
    @6
    @3
    vx
    c0
    cC
    citg
    #
    cc0
    @6
    @2
    c0
    wceq
    @3
    @10
    wceq
    @6
    @2
    cB
    cB
    cioo
    co
    c0
    cA
    cB
    cB
    cioo
    oveq1
    cB
    iooid
    syl6eq
    vx
    @2
    c0
    cC
    itgeq1
    syl
    vx
    cC
    itg0
    syl6eq
    negeqd
    3eqtr4a
    syl6bi
    @0
    wn
    @1
    @0
    vx
    cB
    cA
    cioo
    co
    cC
    citg
    #
    @4
    cif
    @4
    vx
    cB
    cA
    cC
    df-ditg
    @0
    @11
    @4
    iffalse
    syl5eq
    pm2.61d1
end
