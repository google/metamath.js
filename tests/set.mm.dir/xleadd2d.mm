include "cxr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "cxad.mm"
include "co.mm"
include "xleadd2a.mm"
include "syl31anc.mm"

theorem xleadd2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume xleadd2d.1: |- ( ph -> A e. RR* )
  assume xleadd2d.2: |- ( ph -> B e. RR* )
  assume xleadd2d.3: |- ( ph -> C e. RR* )
  assume xleadd2d.4: |- ( ph -> A <_ B )


  assert |- ( ph -> ( C +e A ) <_ ( C +e B ) )

  proof
    wph
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    cC
    cxr
    wcel
    cA
    cB
    cle
    wbr
    cC
    cA
    cxad
    co
    cC
    cB
    cxad
    co
    cle
    wbr
    xleadd2d.1
    xleadd2d.2
    xleadd2d.3
    xleadd2d.4
    cA
    cB
    cC
    xleadd2a
    syl31anc
end
