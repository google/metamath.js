include "cfsupp.mm"
include "wbr.mm"
include "csupp.mm"
include "co.mm"
include "cfn.mm"
include "wcel.mm"
include "fsuppimpd.mm"
include "ressuppfi.mm"
include "wfun.mm"
include "wb.mm"
include "funisfsupp.mm"
include "syl3anc.mm"
include "mpbird.mm"

theorem resfsupp
  let wph: wff ph
  let cB: class B
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let cZ: class Z
  assume resfsupp.b: |- ( ph -> ( dom F \ B ) e. Fin )
  assume resfsupp.e: |- ( ph -> F e. W )
  assume resfsupp.f: |- ( ph -> Fun F )
  assume resfsupp.g: |- ( ph -> G = ( F |` B ) )
  assume resfsupp.s: |- ( ph -> G finSupp Z )
  assume resfsupp.z: |- ( ph -> Z e. V )


  assert |- ( ph -> F finSupp Z )

  proof
    wph
    cF
    cZ
    cfsupp
    wbr
    #
    cF
    cZ
    csupp
    co
    cfn
    wcel
    #
    wph
    cB
    cF
    cG
    cV
    cW
    cZ
    resfsupp.b
    resfsupp.e
    resfsupp.g
    wph
    cG
    cZ
    resfsupp.s
    fsuppimpd
    resfsupp.z
    ressuppfi
    wph
    cF
    wfun
    cF
    cW
    wcel
    cZ
    cV
    wcel
    @0
    @1
    wb
    resfsupp.f
    resfsupp.e
    resfsupp.z
    cF
    cW
    cV
    cZ
    funisfsupp
    syl3anc
    mpbird
end
