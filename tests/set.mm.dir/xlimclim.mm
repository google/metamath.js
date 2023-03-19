include "clsxlim.mm"
include "wbr.mm"
include "cle.mm"
include "cordt.mm"
include "cfv.mm"
include "clm.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cli.mm"
include "wb.mm"
include "df-xlim.mm"
include "breqi.mm"
include "a1i.mm"
include "cvv.mm"
include "cr.mm"
include "xrtgioo2.mm"
include "wcel.mm"
include "reex.mm"
include "ctop.mm"
include "letop.mm"
include "lmss.mm"
include "eqid.mm"
include "climreeq.mm"
include "3bitrd.mm"

theorem xlimclim
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume xlimclim.m: |- ( ph -> M e. ZZ )
  assume xlimclim.z: |- Z = ( ZZ>= ` M )
  assume xlimclim.f: |- ( ph -> F : Z --> RR )
  assume xlimclim.a: |- ( ph -> A e. RR )


  assert |- ( ph -> ( F ~~>* A <-> F ~~> A ) )

  proof
    wph
    cF
    cA
    clsxlim
    wbr
    #
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
    #
    cF
    cA
    cioo
    crn
    ctg
    cfv
    #
    clm
    cfv
    #
    wbr
    cF
    cA
    cli
    wbr
    @0
    @3
    wb
    wph
    cF
    cA
    clsxlim
    @2
    df-xlim
    breqi
    a1i
    wph
    cA
    cF
    @1
    @4
    cM
    cvv
    cr
    cZ
    xrtgioo2
    xlimclim.z
    cr
    cvv
    wcel
    wph
    reex
    a1i
    @1
    ctop
    wcel
    wph
    letop
    a1i
    xlimclim.a
    xlimclim.m
    xlimclim.f
    lmss
    wph
    cA
    @5
    cF
    cM
    cZ
    @5
    eqid
    xlimclim.z
    xlimclim.m
    xlimclim.f
    climreeq
    3bitrd
end
