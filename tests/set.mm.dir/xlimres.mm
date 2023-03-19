include "cle.mm"
include "cordt.mm"
include "cfv.mm"
include "clm.mm"
include "wbr.mm"
include "cuz.mm"
include "cres.mm"
include "clsxlim.mm"
include "cxr.mm"
include "ctopon.mm"
include "wcel.mm"
include "letopon.mm"
include "a1i.mm"
include "lmres.mm"
include "df-xlim.mm"
include "breqi.mm"
include "3bitr4g.mm"

theorem xlimres
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cM: class M
  let vk: setvar k
  let vx: setvar x
  assume xlimres.1: |- ( ph -> F e. ( RR* ^pm CC ) )
  assume xlimres.2: |- ( ph -> M e. ZZ )


  assert |- ( ph -> ( F ~~>* A <-> ( F |` ( ZZ>= ` M ) ) ~~>* A ) )

  proof
    wph
    cF
    cA
    cle
    cordt
    cfv
    #
    clm
    cfv
    #
    wbr
    cF
    cM
    cuz
    cfv
    cres
    #
    cA
    @1
    wbr
    cF
    cA
    clsxlim
    wbr
    @2
    cA
    clsxlim
    wbr
    wph
    cA
    cF
    @0
    cM
    cxr
    @0
    cxr
    ctopon
    cfv
    wcel
    wph
    letopon
    a1i
    xlimres.1
    xlimres.2
    lmres
    cF
    cA
    clsxlim
    @1
    df-xlim
    breqi
    @2
    cA
    clsxlim
    @1
    df-xlim
    breqi
    3bitr4g
end
