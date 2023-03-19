include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "cr.mm"
include "wcel.mm"
include "wo.mm"
include "lelttric.mm"
include "syl2anc.mm"
include "mpjaodan.mm"

theorem ltlecasei
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  assume ltlecasei.1: |- ( ( ph /\ A < B ) -> ps )
  assume ltlecasei.2: |- ( ( ph /\ B <_ A ) -> ps )
  assume ltlecasei.3: |- ( ph -> A e. RR )
  assume ltlecasei.4: |- ( ph -> B e. RR )


  assert |- ( ph -> ps )

  proof
    wph
    cB
    cA
    cle
    wbr
    #
    wps
    cA
    cB
    clt
    wbr
    #
    ltlecasei.2
    ltlecasei.1
    wph
    cB
    cr
    wcel
    cA
    cr
    wcel
    @0
    @1
    wo
    ltlecasei.4
    ltlecasei.3
    cB
    cA
    lelttric
    syl2anc
    mpjaodan
end
