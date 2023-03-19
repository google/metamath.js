include "cxr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "cxad.mm"
include "co.mm"
include "xleadd1a.mm"
include "syl31anc.mm"

theorem xleadd1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume xleadd1d.1: |- ( ph -> A e. RR* )
  assume xleadd1d.2: |- ( ph -> B e. RR* )
  assume xleadd1d.3: |- ( ph -> C e. RR* )
  assume xleadd1d.4: |- ( ph -> A <_ B )


  assert |- ( ph -> ( A +e C ) <_ ( B +e C ) )

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
    cA
    cC
    cxad
    co
    cB
    cC
    cxad
    co
    cle
    wbr
    xleadd1d.1
    xleadd1d.2
    xleadd1d.3
    xleadd1d.4
    cA
    cB
    cC
    xleadd1a
    syl31anc
end
