include "cr.mm"
include "wcel.mm"
include "wceq.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "wb.mm"
include "lttri3.mm"
include "syl2anc.mm"

theorem lttri3d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume ltd.1: |- ( ph -> A e. RR )
  assume ltd.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( A = B <-> ( -. A < B /\ -. B < A ) ) )

  proof
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    cA
    cB
    wceq
    cA
    cB
    clt
    wbr
    wn
    cB
    cA
    clt
    wbr
    wn
    wa
    wb
    ltd.1
    ltd.2
    cA
    cB
    lttri3
    syl2anc
end
