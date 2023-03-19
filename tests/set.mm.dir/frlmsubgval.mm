include "co.mm"
include "crglmod.mm"
include "cfv.mm"
include "cpws.mm"
include "cress.mm"
include "csg.mm"
include "cof.mm"
include "crg.mm"
include "wcel.mm"
include "wceq.mm"
include "frlmpws.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "oveqd.mm"
include "csubg.mm"
include "clmod.mm"
include "clss.mm"
include "rlmlmod.mm"
include "syl.mm"
include "eqid.mm"
include "pwslmod.mm"
include "frlmlss.mm"
include "lsssubg.mm"
include "subgsub.mm"
include "syl3anc.mm"
include "cgrp.mm"
include "cbs.mm"
include "lmodgrp.mm"
include "3syl.mm"
include "cmap.mm"
include "frlmbasmap.mm"
include "rlmbas.mm"
include "pwsbas.mm"
include "eleqtrd.mm"
include "rlmsub.mm"
include "eqtri.mm"
include "pwssub.mm"
include "syl22anc.mm"
include "3eqtr2d.mm"

theorem frlmsubgval
  let wph: wff ph
  let cB: class B
  let cR: class R
  let cF: class F
  let cG: class G
  let cI: class I
  let cM: class M
  let c.mi: class .-
  let cW: class W
  let cY: class Y
  assume frlmsubval.y: |- Y = ( R freeLMod I )
  assume frlmsubval.b: |- B = ( Base ` Y )
  assume frlmsubval.r: |- ( ph -> R e. Ring )
  assume frlmsubval.i: |- ( ph -> I e. W )
  assume frlmsubval.f: |- ( ph -> F e. B )
  assume frlmsubval.g: |- ( ph -> G e. B )
  assume frlmsubval.a: |- .- = ( -g ` R )
  assume frlmsubval.p: |- M = ( -g ` Y )


  assert |- ( ph -> ( F M G ) = ( F oF .- G ) )

  proof
    wph
    cF
    cG
    cM
    co
    cF
    cG
    cR
    crglmod
    cfv
    #
    cI
    cpws
    co
    #
    cB
    cress
    co
    #
    csg
    cfv
    #
    co
    #
    cF
    cG
    @1
    csg
    cfv
    #
    co
    #
    cF
    cG
    c.mi
    cof
    co
    #
    wph
    cM
    @3
    cF
    cG
    wph
    cM
    cY
    csg
    cfv
    @3
    frlmsubval.p
    wph
    cY
    @2
    csg
    wph
    cR
    crg
    wcel
    #
    cI
    cW
    wcel
    #
    cY
    @2
    wceq
    frlmsubval.r
    frlmsubval.i
    cB
    cR
    cY
    cI
    crg
    cW
    frlmsubval.y
    frlmsubval.b
    frlmpws
    syl2anc
    fveq2d
    syl5eq
    oveqd
    wph
    cB
    @1
    csubg
    cfv
    wcel
    #
    cF
    cB
    wcel
    #
    cG
    cB
    wcel
    #
    @6
    @4
    wceq
    wph
    @1
    clmod
    wcel
    #
    cB
    @1
    clss
    cfv
    #
    wcel
    #
    @10
    wph
    @0
    clmod
    wcel
    #
    @9
    @13
    wph
    @8
    @16
    frlmsubval.r
    cR
    rlmlmod
    #
    syl
    frlmsubval.i
    @0
    cI
    cW
    @1
    @1
    eqid
    #
    pwslmod
    syl2anc
    wph
    @8
    @9
    @15
    frlmsubval.r
    frlmsubval.i
    cB
    cR
    @14
    cY
    cI
    cW
    frlmsubval.y
    frlmsubval.b
    @14
    eqid
    #
    frlmlss
    syl2anc
    @14
    cB
    @1
    @19
    lsssubg
    syl2anc
    frlmsubval.f
    frlmsubval.g
    cB
    @1
    @2
    @5
    @3
    cF
    cG
    @5
    eqid
    #
    @2
    eqid
    @3
    eqid
    subgsub
    syl3anc
    wph
    @0
    cgrp
    wcel
    #
    @9
    cF
    @1
    cbs
    cfv
    #
    wcel
    cG
    @22
    wcel
    @6
    @7
    wceq
    wph
    @8
    @16
    @21
    frlmsubval.r
    @17
    @0
    lmodgrp
    3syl
    #
    frlmsubval.i
    wph
    cF
    cR
    cbs
    cfv
    #
    cI
    cmap
    co
    #
    @22
    wph
    @9
    @11
    cF
    @25
    wcel
    frlmsubval.i
    frlmsubval.f
    cB
    cR
    cY
    cI
    @24
    cW
    cF
    frlmsubval.y
    @24
    eqid
    #
    frlmsubval.b
    frlmbasmap
    syl2anc
    wph
    @21
    @9
    @25
    @22
    wceq
    @23
    frlmsubval.i
    @24
    @0
    cI
    cgrp
    cW
    @1
    @18
    cR
    rlmbas
    pwsbas
    syl2anc
    #
    eleqtrd
    wph
    cG
    @25
    @22
    wph
    @9
    @12
    cG
    @25
    wcel
    frlmsubval.i
    frlmsubval.g
    cB
    cR
    cY
    cI
    @24
    cW
    cG
    frlmsubval.y
    @26
    frlmsubval.b
    frlmbasmap
    syl2anc
    @27
    eleqtrd
    @22
    @0
    cF
    cG
    cI
    c.mi
    @5
    cW
    @1
    @18
    @22
    eqid
    c.mi
    cR
    csg
    cfv
    @0
    csg
    cfv
    frlmsubval.a
    cR
    rlmsub
    eqtri
    @20
    pwssub
    syl22anc
    3eqtr2d
end
