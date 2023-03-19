include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "wa.mm"
include "ctrls.mm"
include "wbr.mm"
include "cwlks.mm"
include "wi.mm"
include "trliswlk.mm"
include "cfz.mm"
include "wlkpvtx.mm"
include "elfzofz.mm"
include "impel.mm"
include "fzofzp1.mm"
include "jca.mm"
include "ex.mm"
include "3syl.mm"
include "mpd.mm"

theorem trlsegvdeglem1
  let wph: wff ph
  let cP: class P
  let cU: class U
  let cF: class F
  let cG: class G
  let cI: class I
  let cN: class N
  let cV: class V
  assume trlsegvdeg.v: |- V = ( Vtx ` G )
  assume trlsegvdeg.i: |- I = ( iEdg ` G )
  assume trlsegvdeg.f: |- ( ph -> Fun I )
  assume trlsegvdeg.n: |- ( ph -> N e. ( 0 ..^ ( # ` F ) ) )
  assume trlsegvdeg.u: |- ( ph -> U e. V )
  assume trlsegvdeg.w: |- ( ph -> F ( Trails ` G ) P )


  assert |- ( ph -> ( ( P ` N ) e. V /\ ( P ` ( N + 1 ) ) e. V ) )

  proof
    wph
    cN
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    wcel
    #
    cN
    cP
    cfv
    cV
    wcel
    #
    cN
    c1
    caddc
    co
    #
    cP
    cfv
    cV
    wcel
    #
    wa
    #
    trlsegvdeg.n
    wph
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    @1
    @5
    wi
    trlsegvdeg.w
    cP
    cF
    cG
    trliswlk
    @6
    @1
    @5
    @6
    @1
    wa
    @2
    @4
    @6
    cN
    cc0
    @0
    cfz
    co
    #
    wcel
    @2
    @1
    cP
    cF
    cG
    cN
    cV
    trlsegvdeg.v
    wlkpvtx
    cN
    cc0
    @0
    elfzofz
    impel
    @6
    @3
    @7
    wcel
    @4
    @1
    cP
    cF
    cG
    @3
    cV
    trlsegvdeg.v
    wlkpvtx
    cc0
    @0
    cN
    fzofzp1
    impel
    jca
    ex
    3syl
    mpd
end
