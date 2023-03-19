include "cxad.mm"
include "co.mm"
include "cle.mm"
include "xadd0ge.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "cxr.mm"
include "iccssxr.mm"
include "sseldi.mm"
include "xaddcomd.mm"
include "breqtrd.mm"

theorem xadd0ge2
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume xadd0ge2.a: |- ( ph -> A e. RR* )
  assume xadd0ge2.b: |- ( ph -> B e. ( 0 [,] +oo ) )


  assert |- ( ph -> A <_ ( B +e A ) )

  proof
    wph
    cA
    cA
    cB
    cxad
    co
    cB
    cA
    cxad
    co
    cle
    wph
    cA
    cB
    xadd0ge2.a
    xadd0ge2.b
    xadd0ge
    wph
    cA
    cB
    xadd0ge2.a
    wph
    cc0
    cpnf
    cicc
    co
    cxr
    cB
    cc0
    cpnf
    iccssxr
    xadd0ge2.b
    sseldi
    xaddcomd
    breqtrd
end
