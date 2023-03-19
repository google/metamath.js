include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cprds.mm"
include "co.mm"
include "cds.mm"
include "cbs.mm"
include "cme.mm"
include "cxp.mm"
include "cres.mm"
include "cmt.mm"
include "eqid.mm"
include "ffvelrnda.mm"
include "wcel.mm"
include "wa.mm"
include "msmet.mm"
include "syl.mm"
include "prdsmet.mm"
include "feqmptd.mm"
include "oveq2d.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "3eltr4d.mm"

theorem prdsmslem1
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cR: class R
  let cS: class S
  let cI: class I
  let cW: class W
  let cY: class Y
  let vg: setvar g
  let vk: setvar k
  let vp: setvar p
  let vr: setvar r
  let vw: setvar w
  let vy: setvar y
  let vm: setvar m
  let vu: setvar u
  let vx: setvar x
  let vn: setvar n
  let vz: setvar z
  let cC: class C
  let cE: class E
  let cK: class K
  let cV: class V
  assume prdsxms.y: |- Y = ( S Xs_ R )
  assume prdsxms.s: |- ( ph -> S e. W )
  assume prdsxms.i: |- ( ph -> I e. Fin )
  assume prdsxms.d: |- D = ( dist ` Y )
  assume prdsxms.b: |- B = ( Base ` Y )
  assume prdsms.r: |- ( ph -> R : I --> MetSp )


  assert |- ( ph -> D e. ( Met ` B ) )

  proof
    wph
    cS
    vk
    cI
    vk
    cv
    #
    cR
    cfv
    #
    cmpt
    #
    cprds
    co
    #
    cds
    cfv
    #
    @3
    cbs
    cfv
    #
    cme
    cfv
    cD
    cB
    cme
    cfv
    wph
    vk
    @5
    @4
    @1
    cS
    @1
    cds
    cfv
    @1
    cbs
    cfv
    #
    @6
    cxp
    cres
    #
    cI
    @6
    cW
    @3
    cmt
    @3
    eqid
    @5
    eqid
    @6
    eqid
    #
    @7
    eqid
    #
    @4
    eqid
    prdsxms.s
    prdsxms.i
    wph
    cI
    cmt
    @0
    cR
    prdsms.r
    ffvelrnda
    #
    wph
    @0
    cI
    wcel
    wa
    @1
    cmt
    wcel
    @7
    @6
    cme
    cfv
    wcel
    @10
    @7
    @1
    @6
    @8
    @9
    msmet
    syl
    prdsmet
    wph
    cD
    cY
    cds
    cfv
    @4
    prdsxms.d
    wph
    cY
    @3
    cds
    wph
    cY
    cS
    cR
    cprds
    co
    @3
    prdsxms.y
    wph
    cR
    @2
    cS
    cprds
    wph
    vk
    cI
    cmt
    cR
    prdsms.r
    feqmptd
    oveq2d
    syl5eq
    #
    fveq2d
    syl5eq
    wph
    cB
    @5
    cme
    wph
    cB
    cY
    cbs
    cfv
    @5
    prdsxms.b
    wph
    cY
    @3
    cbs
    @11
    fveq2d
    syl5eq
    fveq2d
    3eltr4d
end
