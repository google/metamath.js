include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cbs.mm"
include "wral.mm"
include "cixp.mm"
include "prdsbas2.mm"
include "eleqtrd.mm"
include "cvv.mm"
include "wfn.mm"
include "elixp2.mm"
include "simp3bi.mm"
include "syl.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eleq12d.mm"
include "rspcva.mm"
include "syl2anc.mm"

theorem prdsbasprj
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let cI: class I
  let cJ: class J
  let cV: class V
  let cW: class W
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cG: class G
  let cK: class K
  assume prdsbasmpt.y: |- Y = ( S Xs_ R )
  assume prdsbasmpt.b: |- B = ( Base ` Y )
  assume prdsbasmpt.s: |- ( ph -> S e. V )
  assume prdsbasmpt.i: |- ( ph -> I e. W )
  assume prdsbasmpt.r: |- ( ph -> R Fn I )
  assume prdsbasmpt.t: |- ( ph -> T e. B )
  assume prdsbasprj.j: |- ( ph -> J e. I )


  assert |- ( ph -> ( T ` J ) e. ( Base ` ( R ` J ) ) )

  proof
    wph
    cJ
    cI
    wcel
    vx
    cv
    #
    cT
    cfv
    #
    @0
    cR
    cfv
    #
    cbs
    cfv
    #
    wcel
    #
    vx
    cI
    wral
    #
    cJ
    cT
    cfv
    #
    cJ
    cR
    cfv
    #
    cbs
    cfv
    #
    wcel
    #
    prdsbasprj.j
    wph
    cT
    vx
    cI
    @3
    cixp
    #
    wcel
    #
    @5
    wph
    cT
    cB
    @10
    prdsbasmpt.t
    wph
    vx
    cB
    cR
    cS
    cI
    cV
    cW
    cY
    prdsbasmpt.y
    prdsbasmpt.b
    prdsbasmpt.s
    prdsbasmpt.i
    prdsbasmpt.r
    prdsbas2
    eleqtrd
    @11
    cT
    cvv
    wcel
    cT
    cI
    wfn
    @5
    vx
    cI
    @3
    cT
    elixp2
    simp3bi
    syl
    @4
    @9
    vx
    cJ
    cI
    @0
    cJ
    wceq
    #
    @1
    @6
    @3
    @8
    @0
    cJ
    cT
    fveq2
    @12
    @2
    @7
    cbs
    @0
    cJ
    cR
    fveq2
    fveq2d
    eleq12d
    rspcva
    syl2anc
end
