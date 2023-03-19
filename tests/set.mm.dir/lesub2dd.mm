include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "lesub2d.mm"
include "mpbid.mm"

theorem lesub2dd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume leidd.1: |- ( ph -> A e. RR )
  assume ltnegd.2: |- ( ph -> B e. RR )
  assume ltadd1d.3: |- ( ph -> C e. RR )
  assume leadd1dd.4: |- ( ph -> A <_ B )


  assert |- ( ph -> ( C - B ) <_ ( C - A ) )

  proof
    wph
    cA
    cB
    cle
    wbr
    cC
    cB
    cmin
    co
    cC
    cA
    cmin
    co
    cle
    wbr
    leadd1dd.4
    wph
    cA
    cB
    cC
    leidd.1
    ltnegd.2
    ltadd1d.3
    lesub2d
    mpbid
end
