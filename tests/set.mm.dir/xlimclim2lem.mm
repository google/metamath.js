include "cv.mm"
include "cuz.mm"
include "cfv.mm"
include "cr.mm"
include "cres.mm"
include "wf.mm"
include "clsxlim.mm"
include "wbr.mm"
include "cli.mm"
include "wb.mm"
include "wcel.mm"
include "wa.mm"
include "cxr.mm"
include "cc.mm"
include "cpm.mm"
include "co.mm"
include "fuzxrpmcn.mm"
include "ad2antrr.mm"
include "cz.mm"
include "eluzelz2.mm"
include "ad2antlr.mm"
include "xlimres.mm"
include "eqid.mm"
include "simpr.mm"
include "xlimclim.mm"
include "cvv.mm"
include "fvexi.mm"
include "a1i.mm"
include "fexd.mm"
include "climres.mm"
include "syl2anr.mm"
include "adantr.mm"
include "3bitrd.mm"
include "r19.29a.mm"

theorem xlimclim2lem
  let wph: wff ph
  let cA: class A
  let vj: setvar j
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume xlimclim2lem.z: |- Z = ( ZZ>= ` M )
  assume xlimclim2lem.f: |- ( ph -> F : Z --> RR* )
  assume xlimclim2lem.a: |- ( ph -> A e. RR )
  assume xlimclim2lem.r: |- ( ph -> E. j e. Z ( F |` ( ZZ>= ` j ) ) : ( ZZ>= ` j ) --> RR )

  disjoint A j
  disjoint F j
  disjoint j ph
  disjoint k x
  assert |- ( ph -> ( F ~~>* A <-> F ~~> A ) )

  proof
    wph
    vj
    cv
    #
    cuz
    cfv
    #
    cr
    cF
    @1
    cres
    #
    wf
    #
    cF
    cA
    clsxlim
    wbr
    #
    cF
    cA
    cli
    wbr
    #
    wb
    vj
    cZ
    wph
    @0
    cZ
    wcel
    #
    wa
    #
    @3
    wa
    #
    @4
    @2
    cA
    clsxlim
    wbr
    @2
    cA
    cli
    wbr
    #
    @5
    @8
    cA
    cF
    @0
    wph
    cF
    cxr
    cc
    cpm
    co
    wcel
    @6
    @3
    wph
    cF
    cM
    cZ
    xlimclim2lem.z
    xlimclim2lem.f
    fuzxrpmcn
    ad2antrr
    @6
    @0
    cz
    wcel
    #
    wph
    @3
    cM
    @0
    cZ
    xlimclim2lem.z
    eluzelz2
    #
    ad2antlr
    #
    xlimres
    @8
    cA
    @2
    @0
    @1
    @12
    @1
    eqid
    @7
    @3
    simpr
    wph
    cA
    cr
    wcel
    @6
    @3
    xlimclim2lem.a
    ad2antrr
    xlimclim
    @7
    @9
    @5
    wb
    #
    @3
    @6
    @10
    cF
    cvv
    wcel
    @13
    wph
    @11
    wph
    cZ
    cxr
    cvv
    cF
    xlimclim2lem.f
    cZ
    cvv
    wcel
    wph
    cZ
    cM
    cuz
    xlimclim2lem.z
    fvexi
    a1i
    fexd
    cA
    cF
    @0
    cvv
    climres
    syl2anr
    adantr
    3bitrd
    xlimclim2lem.r
    r19.29a
end
