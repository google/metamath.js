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
include "fco.mm"
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

theorem fsuppco2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cU: class U
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vx: setvar x
  assume fsuppco2.z: |- ( ph -> Z e. W )
  assume fsuppco2.f: |- ( ph -> F : A --> B )
  assume fsuppco2.g: |- ( ph -> G : B --> B )
  assume fsuppco2.a: |- ( ph -> A e. U )
  assume fsuppco2.b: |- ( ph -> B e. V )
  assume fsuppco2.n: |- ( ph -> F finSupp Z )
  assume fsuppco2.i: |- ( ph -> ( G ` Z ) = Z )


  assert |- ( ph -> ( G o. F ) finSupp Z )

  proof
    wph
    cG
    cF
    ccom
    #
    cZ
    cfsupp
    wbr
    #
    @0
    wfun
    #
    @0
    cZ
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
    cB
    cG
    wf
    #
    @5
    fsuppco2.g
    cB
    cB
    cG
    ffun
    syl
    wph
    cA
    cB
    cF
    wf
    #
    @6
    fsuppco2.f
    cA
    cB
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
    fsuppco2.n
    fsuppimpd
    wph
    cA
    cB
    vx
    @0
    @9
    cZ
    wph
    @7
    @8
    cA
    cB
    @0
    wf
    fsuppco2.g
    fsuppco2.f
    cA
    cB
    cB
    cG
    cF
    fco
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
    cZ
    wph
    @8
    @10
    cA
    wcel
    @13
    @15
    wceq
    @11
    fsuppco2.f
    @10
    cA
    @9
    eldifi
    cA
    cB
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
    cB
    cW
    cF
    cU
    @9
    @10
    cZ
    fsuppco2.f
    @9
    @9
    wss
    wph
    @9
    ssid
    a1i
    fsuppco2.a
    fsuppco2.z
    suppssr
    fveq2d
    wph
    @16
    cZ
    wceq
    @11
    fsuppco2.i
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
    cZ
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
    fsuppco2.g
    fsuppco2.b
    cB
    cB
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
    fsuppco2.f
    fsuppco2.a
    cA
    cB
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
    fsuppco2.z
    @0
    cvv
    cW
    cZ
    isfsupp
    syl2anc
    mpbir2and
end
