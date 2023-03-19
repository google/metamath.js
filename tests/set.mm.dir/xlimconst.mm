include "cle.mm"
include "cordt.mm"
include "cfv.mm"
include "clm.mm"
include "wbr.mm"
include "clsxlim.mm"
include "csn.mm"
include "cxp.mm"
include "cxr.mm"
include "fconst7.mm"
include "ctopon.mm"
include "wcel.mm"
include "cz.mm"
include "letopon.mm"
include "lmconst.mm"
include "mp3an2i.mm"
include "eqbrtrd.mm"
include "df-xlim.mm"
include "breqi.mm"
include "sylibr.mm"

theorem xlimconst
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vx: setvar x
  assume xlimconst.p: |- F/ k ph
  assume xlimconst.k: |- F/_ k F
  assume xlimconst.m: |- ( ph -> M e. ZZ )
  assume xlimconst.z: |- Z = ( ZZ>= ` M )
  assume xlimconst.f: |- ( ph -> F Fn Z )
  assume xlimconst.a: |- ( ph -> A e. RR* )
  assume xlimconst.e: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = A )

  disjoint A k
  disjoint Z k
  disjoint k x
  assert |- ( ph -> F ~~>* A )

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
    cA
    clsxlim
    wbr
    wph
    cF
    cZ
    cA
    csn
    cxp
    #
    cA
    @1
    wph
    vk
    cZ
    cA
    cF
    cxr
    xlimconst.p
    xlimconst.k
    xlimconst.f
    xlimconst.a
    xlimconst.e
    fconst7
    @0
    cxr
    ctopon
    cfv
    wcel
    wph
    cA
    cxr
    wcel
    cM
    cz
    wcel
    @2
    cA
    @1
    wbr
    letopon
    xlimconst.a
    xlimconst.m
    cA
    @0
    cM
    cxr
    cZ
    xlimconst.z
    lmconst
    mp3an2i
    eqbrtrd
    cF
    cA
    clsxlim
    @1
    df-xlim
    breqi
    sylibr
end
