include "cxad.mm"
include "co.mm"
include "xaddcld.mm"
include "xleadd2d.mm"
include "xleadd1d.mm"
include "xrletrd.mm"

theorem xle2addd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume xle2addd.1: |- ( ph -> A e. RR* )
  assume xle2addd.2: |- ( ph -> B e. RR* )
  assume xle2addd.3: |- ( ph -> C e. RR* )
  assume xle2addd.4: |- ( ph -> D e. RR* )
  assume xle2addd.5: |- ( ph -> A <_ C )
  assume xrle2addd.6: |- ( ph -> B <_ D )


  assert |- ( ph -> ( A +e B ) <_ ( C +e D ) )

  proof
    wph
    cA
    cB
    cxad
    co
    cA
    cD
    cxad
    co
    cC
    cD
    cxad
    co
    wph
    cA
    cB
    xle2addd.1
    xle2addd.2
    xaddcld
    wph
    cA
    cD
    xle2addd.1
    xle2addd.4
    xaddcld
    wph
    cC
    cD
    xle2addd.3
    xle2addd.4
    xaddcld
    wph
    cB
    cD
    cA
    xle2addd.2
    xle2addd.4
    xle2addd.1
    xrle2addd.6
    xleadd2d
    wph
    cA
    cC
    cD
    xle2addd.1
    xle2addd.3
    xle2addd.4
    xle2addd.5
    xleadd1d
    xrletrd
end
