include "csle.mm"
include "wbr.mm"
include "cslt.mm"
include "csur.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "slelttr.mm"
include "syl3anc.mm"
include "mp2and.mm"

theorem slelttrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume slttrd.1: |- ( ph -> A e. No )
  assume slttrd.2: |- ( ph -> B e. No )
  assume slttrd.3: |- ( ph -> C e. No )
  assume slelttrd.4: |- ( ph -> A <_s B )
  assume slelttrd.5: |- ( ph -> B <s C )


  assert |- ( ph -> A <s C )

  proof
    wph
    cA
    cB
    csle
    wbr
    #
    cB
    cC
    cslt
    wbr
    #
    cA
    cC
    cslt
    wbr
    #
    slelttrd.4
    slelttrd.5
    wph
    cA
    csur
    wcel
    cB
    csur
    wcel
    cC
    csur
    wcel
    @0
    @1
    wa
    @2
    wi
    slttrd.1
    slttrd.2
    slttrd.3
    cA
    cB
    cC
    slelttr
    syl3anc
    mp2and
end
