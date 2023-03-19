include "cslt.mm"
include "wbr.mm"
include "csur.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "slttr.mm"
include "syl3anc.mm"
include "mp2and.mm"

theorem slttrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume slttrd.1: |- ( ph -> A e. No )
  assume slttrd.2: |- ( ph -> B e. No )
  assume slttrd.3: |- ( ph -> C e. No )
  assume slttrd.4: |- ( ph -> A <s B )
  assume slttrd.5: |- ( ph -> B <s C )


  assert |- ( ph -> A <s C )

  proof
    wph
    cA
    cB
    cslt
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
    slttrd.4
    slttrd.5
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
    slttr
    syl3anc
    mp2and
end
