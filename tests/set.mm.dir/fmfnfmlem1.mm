include "cv.mm"
include "cfi.mm"
include "cfv.mm"
include "wcel.mm"
include "cima.mm"
include "wss.mm"
include "wi.mm"
include "wa.mm"
include "wrex.mm"
include "cfbas.mm"
include "fbssfi.mm"
include "sylan.mm"
include "sstr2.mm"
include "imass2.mm"
include "syl11.mm"
include "reximdv.mm"
include "syl5com.mm"
include "cfm.mm"
include "co.mm"
include "wf.mm"
include "wb.mm"
include "cfil.mm"
include "filtop.mm"
include "syl.mm"
include "elfm.mm"
include "syl3anc.mm"
include "sseld.mm"
include "sylbird.mm"
include "expcomd.mm"
include "adantr.mm"
include "syld.mm"
include "ex.mm"

theorem fmfnfmlem1
  let wph: wff ph
  let vt: setvar t
  let cB: class B
  let cF: class F
  let cL: class L
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let vf: setvar f
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume fmfnfm.b: |- ( ph -> B e. ( fBas ` Y ) )
  assume fmfnfm.l: |- ( ph -> L e. ( Fil ` X ) )
  assume fmfnfm.f: |- ( ph -> F : Y --> X )
  assume fmfnfm.fm: |- ( ph -> ( ( X FilMap F ) ` B ) C_ L )

  disjoint s t
  disjoint B s
  disjoint B t
  disjoint F s
  disjoint F t
  disjoint L s
  disjoint L t
  disjoint ph s
  disjoint ph t
  disjoint X s
  disjoint X t
  disjoint Y s
  disjoint Y t
  disjoint f s
  disjoint f t
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint F f
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint L f
  disjoint L w
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint X f
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y f
  disjoint Y w
  disjoint Y x
  disjoint Y z
  assert |- ( ph -> ( s e. ( fi ` B ) -> ( ( F " s ) C_ t -> ( t C_ X -> t e. L ) ) ) )

  proof
    wph
    vs
    cv
    #
    cB
    cfi
    cfv
    wcel
    #
    cF
    @0
    cima
    #
    vt
    cv
    #
    wss
    #
    @3
    cX
    wss
    #
    @3
    cL
    wcel
    #
    wi
    #
    wi
    wph
    @1
    wa
    #
    @4
    cF
    vw
    cv
    #
    cima
    #
    @3
    wss
    #
    vw
    cB
    wrex
    #
    @7
    @8
    @9
    @0
    wss
    #
    vw
    cB
    wrex
    #
    @4
    @12
    wph
    cB
    cY
    cfbas
    cfv
    wcel
    #
    @1
    @14
    fmfnfm.b
    vw
    @0
    cB
    cY
    fbssfi
    sylan
    @4
    @13
    @11
    vw
    cB
    @10
    @2
    wss
    @4
    @11
    @13
    @10
    @2
    @3
    sstr2
    @9
    @0
    cF
    imass2
    syl11
    reximdv
    syl5com
    wph
    @12
    @7
    wi
    @1
    wph
    @5
    @12
    @6
    wph
    @5
    @12
    wa
    #
    @3
    cB
    cX
    cF
    cfm
    co
    cfv
    #
    wcel
    #
    @6
    wph
    cX
    cL
    wcel
    #
    @15
    cY
    cX
    cF
    wf
    @18
    @16
    wb
    wph
    cL
    cX
    cfil
    cfv
    wcel
    @19
    fmfnfm.l
    cL
    cX
    filtop
    syl
    fmfnfm.b
    fmfnfm.f
    vw
    @3
    cB
    cL
    cF
    cX
    cY
    elfm
    syl3anc
    wph
    @17
    cL
    @3
    fmfnfm.fm
    sseld
    sylbird
    expcomd
    adantr
    syld
    ex
end
