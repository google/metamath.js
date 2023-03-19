include "csn.mm"
include "cxp.mm"
include "cfsupp.mm"
include "wbr.mm"
include "wfun.mm"
include "csupp.mm"
include "co.mm"
include "cfn.mm"
include "wcel.mm"
include "wfn.mm"
include "fnconstg.mm"
include "fnfun.mm"
include "3syl.mm"
include "c0.mm"
include "fczsupp0.mm"
include "0fin.mm"
include "eqeltri.mm"
include "a1i.mm"
include "cvv.mm"
include "wa.mm"
include "wb.mm"
include "snex.mm"
include "xpexg.mm"
include "sylancl.mm"
include "isfsupp.mm"
include "syl2anc.mm"
include "mpbir2and.mm"

theorem fczfsuppd
  let wph: wff ph
  let cB: class B
  let cV: class V
  let cW: class W
  let cZ: class Z
  assume fczfsuppd.b: |- ( ph -> B e. V )
  assume fczfsuppd.z: |- ( ph -> Z e. W )


  assert |- ( ph -> ( B X. { Z } ) finSupp Z )

  proof
    wph
    cB
    cZ
    csn
    #
    cxp
    #
    cZ
    cfsupp
    wbr
    #
    @1
    wfun
    #
    @1
    cZ
    csupp
    co
    #
    cfn
    wcel
    #
    wph
    cZ
    cW
    wcel
    #
    @1
    cB
    wfn
    @3
    fczfsuppd.z
    cB
    cZ
    cW
    fnconstg
    cB
    @1
    fnfun
    3syl
    @5
    wph
    @4
    c0
    cfn
    cB
    cZ
    fczsupp0
    0fin
    eqeltri
    a1i
    wph
    @1
    cvv
    wcel
    #
    @6
    @2
    @3
    @5
    wa
    wb
    wph
    cB
    cV
    wcel
    @0
    cvv
    wcel
    @7
    fczfsuppd.b
    cZ
    snex
    cB
    @0
    cV
    cvv
    xpexg
    sylancl
    fczfsuppd.z
    @1
    cvv
    cW
    cZ
    isfsupp
    syl2anc
    mpbir2and
end
