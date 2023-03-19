include "cfv.mm"
include "co.mm"
include "fveq1i.mm"
include "csg.mm"
include "eqid.mm"
include "clvec.mm"
include "wcel.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "cbs.mm"
include "cdr.mm"
include "wne.mm"
include "lvecdrng.mm"
include "lflcl.mm"
include "syl3anc.mm"
include "drnginvrcl.mm"
include "lmodmcl.mm"
include "ldualvscl.mm"
include "ldualvsubval.mm"
include "ldualvsval.mm"
include "cur.mm"
include "wceq.mm"
include "drnginvrr.mm"
include "oveq1d.mm"
include "crg.mm"
include "lmodring.mm"
include "ringass.mm"
include "syl13anc.mm"
include "ringlidm.mm"
include "syl2anc.mm"
include "3eqtr3d.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "cgrp.mm"
include "lmodfgrp.mm"
include "grpsubid.mm"
include "3eqtrd.mm"
include "syl5eq.mm"

theorem lcfrlem1
  let wph: wff ph
  let cD: class D
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let c.mi: class .-
  let cV: class V
  let cX: class X
  let c.0: class .0.
  assume lcfrlem1.v: |- V = ( Base ` U )
  assume lcfrlem1.s: |- S = ( Scalar ` U )
  assume lcfrlem1.q: |- .X. = ( .r ` S )
  assume lcfrlem1.z: |- .0. = ( 0g ` S )
  assume lcfrlem1.i: |- I = ( invr ` S )
  assume lcfrlem1.f: |- F = ( LFnl ` U )
  assume lcfrlem1.d: |- D = ( LDual ` U )
  assume lcfrlem1.t: |- .x. = ( .s ` D )
  assume lcfrlem1.m: |- .- = ( -g ` D )
  assume lcfrlem1.u: |- ( ph -> U e. LVec )
  assume lcfrlem1.e: |- ( ph -> E e. F )
  assume lcfrlem1.g: |- ( ph -> G e. F )
  assume lcfrlem1.x: |- ( ph -> X e. V )
  assume lcfrlem1.n: |- ( ph -> ( G ` X ) =/= .0. )
  assume lcfrlem1.h: |- H = ( E .- ( ( ( I ` ( G ` X ) ) .X. ( E ` X ) ) .x. G ) )


  assert |- ( ph -> ( H ` X ) = .0. )

  proof
    wph
    cX
    cH
    cfv
    cX
    cE
    cX
    cG
    cfv
    #
    cI
    cfv
    #
    cX
    cE
    cfv
    #
    c.xp
    co
    #
    cG
    c.x
    co
    #
    c.mi
    co
    #
    cfv
    #
    c.0
    cX
    cH
    @5
    lcfrlem1.h
    fveq1i
    wph
    @6
    @2
    cX
    @4
    cfv
    #
    cS
    csg
    cfv
    #
    co
    @2
    @2
    @8
    co
    #
    c.0
    wph
    cD
    cS
    @8
    cF
    cE
    @4
    c.mi
    cV
    cU
    cX
    lcfrlem1.v
    lcfrlem1.s
    @8
    eqid
    #
    lcfrlem1.f
    lcfrlem1.d
    lcfrlem1.m
    wph
    cU
    clvec
    wcel
    #
    cU
    clmod
    wcel
    #
    lcfrlem1.u
    cU
    lveclmod
    syl
    #
    lcfrlem1.e
    wph
    cD
    cS
    c.x
    cF
    cG
    cS
    cbs
    cfv
    #
    cU
    @3
    lcfrlem1.f
    lcfrlem1.s
    @14
    eqid
    #
    lcfrlem1.d
    lcfrlem1.t
    @13
    wph
    @12
    @1
    @14
    wcel
    #
    @2
    @14
    wcel
    #
    @3
    @14
    wcel
    @13
    wph
    cS
    cdr
    wcel
    #
    @0
    @14
    wcel
    #
    @0
    c.0
    wne
    #
    @16
    wph
    @11
    @18
    lcfrlem1.u
    cS
    cU
    lcfrlem1.s
    lvecdrng
    syl
    #
    wph
    @11
    cG
    cF
    wcel
    cX
    cV
    wcel
    #
    @19
    lcfrlem1.u
    lcfrlem1.g
    lcfrlem1.x
    cS
    cF
    cG
    @14
    cV
    cU
    cX
    clvec
    lcfrlem1.s
    @15
    lcfrlem1.v
    lcfrlem1.f
    lflcl
    syl3anc
    #
    lcfrlem1.n
    @14
    cS
    cI
    @0
    c.0
    @15
    lcfrlem1.z
    lcfrlem1.i
    drnginvrcl
    syl3anc
    #
    wph
    @11
    cE
    cF
    wcel
    @22
    @17
    lcfrlem1.u
    lcfrlem1.e
    lcfrlem1.x
    cS
    cF
    cE
    @14
    cV
    cU
    cX
    clvec
    lcfrlem1.s
    @15
    lcfrlem1.v
    lcfrlem1.f
    lflcl
    syl3anc
    #
    c.xp
    cS
    @14
    cU
    @1
    @2
    lcfrlem1.s
    @15
    lcfrlem1.q
    lmodmcl
    syl3anc
    #
    lcfrlem1.g
    ldualvscl
    lcfrlem1.x
    ldualvsubval
    wph
    @7
    @2
    @2
    @8
    wph
    @7
    @0
    @3
    c.xp
    co
    #
    @2
    wph
    cX
    cD
    cS
    c.x
    c.xp
    cF
    cG
    @14
    cV
    cU
    @3
    clvec
    lcfrlem1.f
    lcfrlem1.v
    lcfrlem1.s
    @15
    lcfrlem1.q
    lcfrlem1.d
    lcfrlem1.t
    lcfrlem1.u
    @26
    lcfrlem1.g
    lcfrlem1.x
    ldualvsval
    wph
    @0
    @1
    c.xp
    co
    #
    @2
    c.xp
    co
    #
    cS
    cur
    cfv
    #
    @2
    c.xp
    co
    #
    @27
    @2
    wph
    @28
    @30
    @2
    c.xp
    wph
    @18
    @19
    @20
    @28
    @30
    wceq
    @21
    @23
    lcfrlem1.n
    @14
    cS
    c.xp
    @30
    cI
    @0
    c.0
    @15
    lcfrlem1.z
    lcfrlem1.q
    @30
    eqid
    #
    lcfrlem1.i
    drnginvrr
    syl3anc
    oveq1d
    wph
    cS
    crg
    wcel
    #
    @19
    @16
    @17
    @29
    @27
    wceq
    wph
    @12
    @33
    @13
    cS
    cU
    lcfrlem1.s
    lmodring
    syl
    #
    @23
    @24
    @25
    @14
    cS
    c.xp
    @0
    @1
    @2
    @15
    lcfrlem1.q
    ringass
    syl13anc
    wph
    @33
    @17
    @31
    @2
    wceq
    @34
    @25
    @14
    cS
    c.xp
    @30
    @2
    @15
    lcfrlem1.q
    @32
    ringlidm
    syl2anc
    3eqtr3d
    eqtrd
    oveq2d
    wph
    cS
    cgrp
    wcel
    #
    @17
    @9
    c.0
    wceq
    wph
    @12
    @35
    @13
    cS
    cU
    lcfrlem1.s
    lmodfgrp
    syl
    @25
    @14
    cS
    @8
    @2
    c.0
    @15
    lcfrlem1.z
    @10
    grpsubid
    syl2anc
    3eqtrd
    syl5eq
end
