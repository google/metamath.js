include "csle.mm"
include "wbr.mm"
include "csur.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "sletr.mm"
include "syl3anc.mm"
include "mp2and.mm"

theorem sletrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume slttrd.1: |- ( ph -> A e. No )
  assume slttrd.2: |- ( ph -> B e. No )
  assume slttrd.3: |- ( ph -> C e. No )
  assume sletrd.4: |- ( ph -> A <_s B )
  assume sletrd.5: |- ( ph -> B <_s C )


  assert |- ( ph -> A <_s C )

  proof
    wph
    cA
    cB
    csle
    wbr
    #
    cB
    cC
    csle
    wbr
    #
    cA
    cC
    csle
    wbr
    #
    sletrd.4
    sletrd.5
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
    sletr
    syl3anc
    mp2and
end
