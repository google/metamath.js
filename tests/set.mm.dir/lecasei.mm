include "cle.mm"
include "wbr.mm"
include "cr.mm"
include "wcel.mm"
include "wo.mm"
include "letric.mm"
include "syl2anc.mm"
include "mpjaodan.mm"

theorem lecasei
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  assume lecase.1: |- ( ph -> A e. RR )
  assume lecase.2: |- ( ph -> B e. RR )
  assume lecase.3: |- ( ( ph /\ A <_ B ) -> ps )
  assume lecase.4: |- ( ( ph /\ B <_ A ) -> ps )


  assert |- ( ph -> ps )

  proof
    wph
    cA
    cB
    cle
    wbr
    #
    wps
    cB
    cA
    cle
    wbr
    #
    lecase.3
    lecase.4
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    @0
    @1
    wo
    lecase.1
    lecase.2
    cA
    cB
    letric
    syl2anc
    mpjaodan
end
