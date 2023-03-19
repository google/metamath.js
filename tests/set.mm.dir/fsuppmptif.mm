include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "cif.mm"
include "cmpt.mm"
include "cfsupp.mm"
include "wbr.mm"
include "wfun.mm"
include "csupp.mm"
include "co.mm"
include "cfn.mm"
include "cvv.mm"
include "wf.mm"
include "wa.mm"
include "fvex.mm"
include "adantr.mm"
include "ifexg.mm"
include "sylancr.mm"
include "eqid.mm"
include "fmptd.mm"
include "ffun.mm"
include "syl.mm"
include "wss.mm"
include "fsuppimpd.mm"
include "cdif.mm"
include "ssid.mm"
include "a1i.mm"
include "suppssr.mm"
include "ifeq1d.mm"
include "ifid.mm"
include "syl6eq.mm"
include "suppss2.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "wb.mm"
include "mptexg.mm"
include "isfsupp.mm"
include "mpbir2and.mm"

theorem fsuppmptif
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let vk: setvar k
  let cF: class F
  let cV: class V
  let cW: class W
  let cZ: class Z
  assume fsuppmptif.f: |- ( ph -> F : A --> B )
  assume fsuppmptif.a: |- ( ph -> A e. V )
  assume fsuppmptif.z: |- ( ph -> Z e. W )
  assume fsuppmptif.s: |- ( ph -> F finSupp Z )

  disjoint A k
  disjoint F k
  disjoint Z k
  disjoint k ph
  assert |- ( ph -> ( k e. A |-> if ( k e. D , ( F ` k ) , Z ) ) finSupp Z )

  proof
    wph
    vk
    cA
    vk
    cv
    #
    cD
    wcel
    #
    @0
    cF
    cfv
    #
    cZ
    cif
    #
    cmpt
    #
    cZ
    cfsupp
    wbr
    #
    @4
    wfun
    #
    @4
    cZ
    csupp
    co
    #
    cfn
    wcel
    #
    wph
    cA
    cvv
    @4
    wf
    @6
    wph
    vk
    cA
    @3
    cvv
    @4
    wph
    @0
    cA
    wcel
    #
    wa
    @2
    cvv
    wcel
    cZ
    cW
    wcel
    #
    @3
    cvv
    wcel
    @0
    cF
    fvex
    wph
    @10
    @9
    fsuppmptif.z
    adantr
    @1
    @2
    cZ
    cvv
    cW
    ifexg
    sylancr
    @4
    eqid
    fmptd
    cA
    cvv
    @4
    ffun
    syl
    wph
    cF
    cZ
    csupp
    co
    #
    cfn
    wcel
    @7
    @11
    wss
    @8
    wph
    cF
    cZ
    fsuppmptif.s
    fsuppimpd
    wph
    cA
    @3
    vk
    cV
    @11
    cZ
    wph
    @0
    cA
    @11
    cdif
    wcel
    wa
    #
    @3
    @1
    cZ
    cZ
    cif
    cZ
    @12
    @1
    @2
    cZ
    cZ
    wph
    cA
    cB
    cW
    cF
    cV
    @11
    @0
    cZ
    fsuppmptif.f
    @11
    @11
    wss
    wph
    @11
    ssid
    a1i
    fsuppmptif.a
    fsuppmptif.z
    suppssr
    ifeq1d
    @1
    cZ
    ifid
    syl6eq
    fsuppmptif.a
    suppss2
    @11
    @7
    ssfi
    syl2anc
    wph
    @4
    cvv
    wcel
    #
    @10
    @5
    @6
    @8
    wa
    wb
    wph
    cA
    cV
    wcel
    @13
    fsuppmptif.a
    vk
    cA
    @3
    cV
    mptexg
    syl
    fsuppmptif.z
    @4
    cvv
    cW
    cZ
    isfsupp
    syl2anc
    mpbir2and
end
