include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cr.mm"
include "wcel.mm"
include "simp1d.mm"
include "adantr.mm"
include "simp2d.mm"
include "simp3d.mm"
include "simpr.mm"
include "cle.mm"
include "ltletrd.mm"
include "ex.mm"

theorem lelttrdi
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume lelttrdi.r: |- ( ph -> ( A e. RR /\ B e. RR /\ C e. RR ) )
  assume lelttrdi.l: |- ( ph -> B <_ C )


  assert |- ( ph -> ( A < B -> A < C ) )

  proof
    wph
    cA
    cB
    clt
    wbr
    #
    cA
    cC
    clt
    wbr
    wph
    @0
    wa
    cA
    cB
    cC
    wph
    cA
    cr
    wcel
    #
    @0
    wph
    @1
    cB
    cr
    wcel
    #
    cC
    cr
    wcel
    #
    lelttrdi.r
    simp1d
    adantr
    wph
    @2
    @0
    wph
    @1
    @2
    @3
    lelttrdi.r
    simp2d
    adantr
    wph
    @3
    @0
    wph
    @1
    @2
    @3
    lelttrdi.r
    simp3d
    adantr
    wph
    @0
    simpr
    wph
    cB
    cC
    cle
    wbr
    @0
    lelttrdi.l
    adantr
    ltletrd
    ex
end
