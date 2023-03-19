include "ccom.mm"
include "cfsupp.mm"
include "wbr.mm"
include "wfun.mm"
include "csupp.mm"
include "co.mm"
include "cfn.mm"
include "wcel.mm"
include "wf.mm"
include "ffun.mm"
include "syl.mm"
include "funco.mm"
include "syl2anc.mm"
include "wss.mm"
include "fsuppimpd.mm"
include "cres.mm"
include "fssresd.mm"
include "fco2.mm"
include "cv.mm"
include "cdif.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "eldifi.mm"
include "fvco3.mm"
include "syl2an.mm"
include "ssid.mm"
include "a1i.mm"
include "suppssr.mm"
include "fveq2d.mm"
include "adantr.mm"
include "3eqtrd.mm"
include "suppss.mm"
include "ssfi.mm"
include "cvv.mm"
include "wb.mm"
include "fex.mm"
include "coexg.mm"
include "isfsupp.mm"
include "mpbir2and.mm"

theorem fsuppcor
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cU: class U
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let cZ: class Z
  let vx: setvar x
  assume fsuppcor.0: |- ( ph -> .0. e. W )
  assume fsuppcor.z: |- ( ph -> Z e. B )
  assume fsuppcor.f: |- ( ph -> F : A --> C )
  assume fsuppcor.g: |- ( ph -> G : B --> D )
  assume fsuppcor.s: |- ( ph -> C C_ B )
  assume fsuppcor.a: |- ( ph -> A e. U )
  assume fsuppcor.b: |- ( ph -> B e. V )
  assume fsuppcor.n: |- ( ph -> F finSupp Z )
  assume fsuppcor.i: |- ( ph -> ( G ` Z ) = .0. )


  assert |- ( ph -> ( G o. F ) finSupp .0. )

  proof
    wph
    cG
    cF
    ccom
    #
    c.0
    cfsupp
    wbr
    #
    @0
    wfun
    #
    @0
    c.0
    csupp
    co
    #
    cfn
    wcel
    #
    wph
    cG
    wfun
    #
    cF
    wfun
    #
    @2
    wph
    cB
    cD
    cG
    wf
    #
    @5
    fsuppcor.g
    cB
    cD
    cG
    ffun
    syl
    wph
    cA
    cC
    cF
    wf
    #
    @6
    fsuppcor.f
    cA
    cC
    cF
    ffun
    syl
    cG
    cF
    funco
    syl2anc
    wph
    cF
    cZ
    csupp
    co
    #
    cfn
    wcel
    @3
    @9
    wss
    @4
    wph
    cF
    cZ
    fsuppcor.n
    fsuppimpd
    wph
    cA
    cD
    vx
    @0
    @9
    c.0
    wph
    cC
    cD
    cG
    cC
    cres
    wf
    @8
    cA
    cD
    @0
    wf
    wph
    cB
    cD
    cC
    cG
    fsuppcor.g
    fsuppcor.s
    fssresd
    fsuppcor.f
    cA
    cC
    cD
    cG
    cF
    fco2
    syl2anc
    wph
    vx
    cv
    #
    cA
    @9
    cdif
    wcel
    #
    wa
    #
    @10
    @0
    cfv
    #
    @10
    cF
    cfv
    #
    cG
    cfv
    #
    cZ
    cG
    cfv
    #
    c.0
    wph
    @8
    @10
    cA
    wcel
    @13
    @15
    wceq
    @11
    fsuppcor.f
    @10
    cA
    @9
    eldifi
    cA
    cC
    @10
    cG
    cF
    fvco3
    syl2an
    @12
    @14
    cZ
    cG
    wph
    cA
    cC
    cB
    cF
    cU
    @9
    @10
    cZ
    fsuppcor.f
    @9
    @9
    wss
    wph
    @9
    ssid
    a1i
    fsuppcor.a
    fsuppcor.z
    suppssr
    fveq2d
    wph
    @16
    c.0
    wceq
    @11
    fsuppcor.i
    adantr
    3eqtrd
    suppss
    @9
    @3
    ssfi
    syl2anc
    wph
    @0
    cvv
    wcel
    #
    c.0
    cW
    wcel
    @1
    @2
    @4
    wa
    wb
    wph
    cG
    cvv
    wcel
    #
    cF
    cvv
    wcel
    #
    @17
    wph
    @7
    cB
    cV
    wcel
    @18
    fsuppcor.g
    fsuppcor.b
    cB
    cD
    cV
    cG
    fex
    syl2anc
    wph
    @8
    cA
    cU
    wcel
    @19
    fsuppcor.f
    fsuppcor.a
    cA
    cC
    cU
    cF
    fex
    syl2anc
    cG
    cF
    cvv
    cvv
    coexg
    syl2anc
    fsuppcor.0
    @0
    cvv
    cW
    c.0
    isfsupp
    syl2anc
    mpbir2and
end
