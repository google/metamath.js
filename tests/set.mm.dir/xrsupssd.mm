include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cle.mm"
include "wbr.mm"
include "wn.mm"
include "wor.mm"
include "xrltso.mm"
include "a1i.mm"
include "wss.mm"
include "cv.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wa.mm"
include "sstrd.mm"
include "xrsupss.mm"
include "syl.mm"
include "supssd.mm"
include "wcel.mm"
include "wb.mm"
include "supcl.mm"
include "xrlenlt.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem xrsupssd
  let wph: wff ph
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume xrsupssd.1: |- ( ph -> B C_ C )
  assume xrsupssd.2: |- ( ph -> C C_ RR* )


  assert |- ( ph -> sup ( B , RR* , < ) <_ sup ( C , RR* , < ) )

  proof
    wph
    cB
    cxr
    clt
    csup
    #
    cC
    cxr
    clt
    csup
    #
    cle
    wbr
    #
    @1
    @0
    clt
    wbr
    wn
    #
    wph
    vx
    vy
    vz
    cxr
    cB
    cC
    clt
    cxr
    clt
    wor
    wph
    xrltso
    a1i
    #
    xrsupssd.1
    xrsupssd.2
    wph
    cB
    cxr
    wss
    vx
    cv
    #
    vy
    cv
    #
    clt
    wbr
    wn
    #
    vy
    cB
    wral
    @6
    @5
    clt
    wbr
    #
    @6
    vz
    cv
    clt
    wbr
    #
    vz
    cB
    wrex
    wi
    vy
    cxr
    wral
    wa
    vx
    cxr
    wrex
    wph
    cB
    cC
    cxr
    xrsupssd.1
    xrsupssd.2
    sstrd
    vx
    vy
    vz
    cB
    xrsupss
    syl
    #
    wph
    cC
    cxr
    wss
    @7
    vy
    cC
    wral
    @8
    @9
    vz
    cC
    wrex
    wi
    vy
    cxr
    wral
    wa
    vx
    cxr
    wrex
    xrsupssd.2
    vx
    vy
    vz
    cC
    xrsupss
    syl
    #
    supssd
    wph
    @0
    cxr
    wcel
    @1
    cxr
    wcel
    @2
    @3
    wb
    wph
    vx
    vy
    vz
    cxr
    cB
    clt
    @4
    @10
    supcl
    wph
    vx
    vy
    vz
    cxr
    cC
    clt
    @4
    @11
    supcl
    @0
    @1
    xrlenlt
    syl2anc
    mpbird
end
