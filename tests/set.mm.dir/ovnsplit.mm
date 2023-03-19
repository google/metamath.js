include "covoln.mm"
include "cfv.mm"
include "cin.mm"
include "cdif.mm"
include "cun.mm"
include "cxad.mm"
include "co.mm"
include "cle.mm"
include "wceq.mm"
include "inundif.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "a1i.mm"
include "cr.mm"
include "cmap.mm"
include "ssinss1d.mm"
include "ssdifssd.mm"
include "ovnsubadd2.mm"
include "eqbrtrd.mm"

theorem ovnsplit
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume ovnsplit.x: |- ( ph -> X e. Fin )
  assume ovnsplit.a: |- ( ph -> A C_ ( RR ^m X ) )


  assert |- ( ph -> ( ( voln* ` X ) ` A ) <_ ( ( ( voln* ` X ) ` ( A i^i B ) ) +e ( ( voln* ` X ) ` ( A \ B ) ) ) )

  proof
    wph
    cA
    cX
    covoln
    cfv
    #
    cfv
    #
    cA
    cB
    cin
    #
    cA
    cB
    cdif
    #
    cun
    #
    @0
    cfv
    #
    @2
    @0
    cfv
    @3
    @0
    cfv
    cxad
    co
    cle
    @1
    @5
    wceq
    wph
    cA
    @4
    @0
    @4
    cA
    cA
    cB
    inundif
    eqcomi
    fveq2i
    a1i
    wph
    @2
    @3
    cX
    ovnsplit.x
    wph
    cA
    cB
    cr
    cX
    cmap
    co
    #
    ovnsplit.a
    ssinss1d
    wph
    cA
    @6
    cB
    ovnsplit.a
    ssdifssd
    ovnsubadd2
    eqbrtrd
end
