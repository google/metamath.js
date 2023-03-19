include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wf.mm"
include "chash.mm"
include "cfv.mm"
include "cword.mm"
include "wcel.mm"
include "wrdf.mm"
include "syl.mm"
include "oveq2d.mm"
include "eqidd.mm"
include "feq23d.mm"
include "mpbird.mm"

theorem wrdfd
  let wph: wff ph
  let cS: class S
  let cN: class N
  let cW: class W
  assume wrdfd.n: |- ( ph -> N = ( # ` W ) )
  assume wrdfd.w: |- ( ph -> W e. Word S )


  assert |- ( ph -> W : ( 0 ..^ N ) --> S )

  proof
    wph
    cc0
    cN
    cfzo
    co
    #
    cS
    cW
    wf
    cc0
    cW
    chash
    cfv
    #
    cfzo
    co
    #
    cS
    cW
    wf
    #
    wph
    cW
    cS
    cword
    wcel
    @3
    wrdfd.w
    cS
    cW
    wrdf
    syl
    wph
    @0
    cS
    @2
    cS
    cW
    wph
    cN
    @1
    cc0
    cfzo
    wrdfd.n
    oveq2d
    wph
    cS
    eqidd
    feq23d
    mpbird
end
