include "clsxlim.mm"
include "wbr.mm"
include "cuz.mm"
include "cfv.mm"
include "cres.mm"
include "nfcv.mm"
include "nfres.mm"
include "eluzelz2d.mm"
include "eqid.mm"
include "cxr.mm"
include "ffnd.mm"
include "uzssd2.mm"
include "fnssresd.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "fvres.mm"
include "adantl.mm"
include "eqtrd.mm"
include "xlimconst.mm"
include "fuzxrpmcn.mm"
include "xlimres.mm"
include "mpbird.mm"

theorem xlimconst2
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vx: setvar x
  assume xlimconst2.p: |- F/ k ph
  assume xlimconst2.k: |- F/_ k F
  assume xlimconst2.z: |- Z = ( ZZ>= ` M )
  assume xlimconst2.f: |- ( ph -> F : Z --> RR* )
  assume xlimconst2.n: |- ( ph -> N e. Z )
  assume xlimconst2.a: |- ( ph -> A e. RR* )
  assume xlimconst2.e: |- ( ( ph /\ k e. ( ZZ>= ` N ) ) -> ( F ` k ) = A )

  disjoint A k
  disjoint N k
  disjoint k x
  assert |- ( ph -> F ~~>* A )

  proof
    wph
    cF
    cA
    clsxlim
    wbr
    cF
    cN
    cuz
    cfv
    #
    cres
    #
    cA
    clsxlim
    wbr
    wph
    cA
    vk
    @1
    cN
    @0
    xlimconst2.p
    vk
    cF
    @0
    xlimconst2.k
    vk
    @0
    nfcv
    nfres
    wph
    cM
    cN
    cZ
    xlimconst2.z
    xlimconst2.n
    eluzelz2d
    #
    @0
    eqid
    wph
    cZ
    @0
    cF
    wph
    cZ
    cxr
    cF
    xlimconst2.f
    ffnd
    wph
    cM
    cN
    cZ
    xlimconst2.z
    xlimconst2.n
    uzssd2
    fnssresd
    xlimconst2.a
    wph
    vk
    cv
    #
    @0
    wcel
    #
    wa
    @3
    @1
    cfv
    #
    @3
    cF
    cfv
    #
    cA
    @4
    @5
    @6
    wceq
    wph
    @3
    @0
    cF
    fvres
    adantl
    xlimconst2.e
    eqtrd
    xlimconst
    wph
    cA
    cF
    cN
    wph
    cF
    cM
    cZ
    xlimconst2.z
    xlimconst2.f
    fuzxrpmcn
    @2
    xlimres
    mpbird
end
