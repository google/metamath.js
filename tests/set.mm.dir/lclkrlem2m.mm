include "wcel.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "cgrp.mm"
include "clmod.mm"
include "clvec.mm"
include "lveclmod.mm"
include "syl.mm"
include "lmodgrp.mm"
include "cbs.mm"
include "crg.mm"
include "lmodring.mm"
include "ldualvaddcl.mm"
include "eqid.mm"
include "lflcl.mm"
include "syl3anc.mm"
include "cdr.mm"
include "wne.mm"
include "lvecdrng.mm"
include "drnginvrcl.mm"
include "ringcl.mm"
include "lmodvscl.mm"
include "grpsubcl.mm"
include "syl5eqel.mm"
include "fveq2i.mm"
include "csg.mm"
include "lflsub.mm"
include "syl112anc.mm"
include "cur.mm"
include "lflmul.mm"
include "ringass.mm"
include "syl13anc.mm"
include "drnginvrl.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "ringridm.mm"
include "syl2anc.mm"
include "3eqtrd.mm"
include "ringgrp.mm"
include "grpsubid.mm"
include "syl5eq.mm"
include "jca.mm"

theorem lclkrlem2m
  let wph: wff ph
  let cB: class B
  let cD: class D
  let c.pl: class .+
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let cV: class V
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume lclkrlem2m.v: |- V = ( Base ` U )
  assume lclkrlem2m.t: |- .x. = ( .s ` U )
  assume lclkrlem2m.s: |- S = ( Scalar ` U )
  assume lclkrlem2m.q: |- .X. = ( .r ` S )
  assume lclkrlem2m.z: |- .0. = ( 0g ` S )
  assume lclkrlem2m.i: |- I = ( invr ` S )
  assume lclkrlem2m.m: |- .- = ( -g ` U )
  assume lclkrlem2m.f: |- F = ( LFnl ` U )
  assume lclkrlem2m.d: |- D = ( LDual ` U )
  assume lclkrlem2m.p: |- .+ = ( +g ` D )
  assume lclkrlem2m.x: |- ( ph -> X e. V )
  assume lclkrlem2m.y: |- ( ph -> Y e. V )
  assume lclkrlem2m.e: |- ( ph -> E e. F )
  assume lclkrlem2m.g: |- ( ph -> G e. F )
  assume lclkrlem2m.w: |- ( ph -> U e. LVec )
  assume lclkrlem2m.b: |- B = ( X .- ( ( ( ( E .+ G ) ` X ) .X. ( I ` ( ( E .+ G ) ` Y ) ) ) .x. Y ) )
  assume lclkrlem2m.n: |- ( ph -> ( ( E .+ G ) ` Y ) =/= .0. )


  assert |- ( ph -> ( B e. V /\ ( ( E .+ G ) ` B ) = .0. ) )

  proof
    wph
    cB
    cV
    wcel
    cB
    cE
    cG
    c.pl
    co
    #
    cfv
    #
    c.0
    wceq
    wph
    cB
    cX
    cX
    @0
    cfv
    #
    cY
    @0
    cfv
    #
    cI
    cfv
    #
    c.xp
    co
    #
    cY
    c.x
    co
    #
    c.mi
    co
    #
    cV
    lclkrlem2m.b
    wph
    cU
    cgrp
    wcel
    #
    cX
    cV
    wcel
    #
    @6
    cV
    wcel
    #
    @7
    cV
    wcel
    wph
    cU
    clmod
    wcel
    #
    @8
    wph
    cU
    clvec
    wcel
    #
    @11
    lclkrlem2m.w
    cU
    lveclmod
    syl
    #
    cU
    lmodgrp
    syl
    lclkrlem2m.x
    wph
    @11
    @5
    cS
    cbs
    cfv
    #
    wcel
    #
    cY
    cV
    wcel
    #
    @10
    @13
    wph
    cS
    crg
    wcel
    #
    @2
    @14
    wcel
    #
    @4
    @14
    wcel
    #
    @15
    wph
    @11
    @17
    @13
    cS
    cU
    lclkrlem2m.s
    lmodring
    syl
    #
    wph
    @12
    @0
    cF
    wcel
    #
    @9
    @18
    lclkrlem2m.w
    wph
    cD
    c.pl
    cF
    cE
    cG
    cU
    lclkrlem2m.f
    lclkrlem2m.d
    lclkrlem2m.p
    @13
    lclkrlem2m.e
    lclkrlem2m.g
    ldualvaddcl
    #
    lclkrlem2m.x
    cS
    cF
    @0
    @14
    cV
    cU
    cX
    clvec
    lclkrlem2m.s
    @14
    eqid
    #
    lclkrlem2m.v
    lclkrlem2m.f
    lflcl
    syl3anc
    #
    wph
    cS
    cdr
    wcel
    #
    @3
    @14
    wcel
    #
    @3
    c.0
    wne
    #
    @19
    wph
    @12
    @25
    lclkrlem2m.w
    cS
    cU
    lclkrlem2m.s
    lvecdrng
    syl
    #
    wph
    @12
    @21
    @16
    @26
    lclkrlem2m.w
    @22
    lclkrlem2m.y
    cS
    cF
    @0
    @14
    cV
    cU
    cY
    clvec
    lclkrlem2m.s
    @23
    lclkrlem2m.v
    lclkrlem2m.f
    lflcl
    syl3anc
    #
    lclkrlem2m.n
    @14
    cS
    cI
    @3
    c.0
    @23
    lclkrlem2m.z
    lclkrlem2m.i
    drnginvrcl
    syl3anc
    #
    @14
    cS
    c.xp
    @2
    @4
    @23
    lclkrlem2m.q
    ringcl
    syl3anc
    #
    lclkrlem2m.y
    @5
    c.x
    cS
    @14
    cV
    cU
    cY
    lclkrlem2m.v
    lclkrlem2m.s
    lclkrlem2m.t
    @23
    lmodvscl
    syl3anc
    #
    cV
    cU
    c.mi
    cX
    @6
    lclkrlem2m.v
    lclkrlem2m.m
    grpsubcl
    syl3anc
    syl5eqel
    wph
    @1
    @7
    @0
    cfv
    #
    c.0
    cB
    @7
    @0
    lclkrlem2m.b
    fveq2i
    wph
    @33
    @2
    @6
    @0
    cfv
    #
    cS
    csg
    cfv
    #
    co
    #
    @2
    @2
    @35
    co
    #
    c.0
    wph
    @11
    @21
    @9
    @10
    @33
    @36
    wceq
    @13
    @22
    lclkrlem2m.x
    @32
    cS
    cF
    @0
    @35
    c.mi
    cV
    cU
    cX
    @6
    lclkrlem2m.s
    @35
    eqid
    #
    lclkrlem2m.v
    lclkrlem2m.m
    lclkrlem2m.f
    lflsub
    syl112anc
    wph
    @34
    @2
    @2
    @35
    wph
    @34
    @5
    @3
    c.xp
    co
    #
    @2
    cS
    cur
    cfv
    #
    c.xp
    co
    #
    @2
    wph
    @11
    @21
    @15
    @16
    @34
    @39
    wceq
    @13
    @22
    @31
    lclkrlem2m.y
    cS
    @5
    c.x
    c.xp
    cF
    @0
    @14
    cV
    cU
    cY
    lclkrlem2m.s
    @23
    lclkrlem2m.q
    lclkrlem2m.v
    lclkrlem2m.t
    lclkrlem2m.f
    lflmul
    syl112anc
    wph
    @39
    @2
    @4
    @3
    c.xp
    co
    #
    c.xp
    co
    #
    @41
    wph
    @17
    @18
    @19
    @26
    @39
    @43
    wceq
    @20
    @24
    @30
    @29
    @14
    cS
    c.xp
    @2
    @4
    @3
    @23
    lclkrlem2m.q
    ringass
    syl13anc
    wph
    @42
    @40
    @2
    c.xp
    wph
    @25
    @26
    @27
    @42
    @40
    wceq
    @28
    @29
    lclkrlem2m.n
    @14
    cS
    c.xp
    @40
    cI
    @3
    c.0
    @23
    lclkrlem2m.z
    lclkrlem2m.q
    @40
    eqid
    #
    lclkrlem2m.i
    drnginvrl
    syl3anc
    oveq2d
    eqtrd
    wph
    @17
    @18
    @41
    @2
    wceq
    @20
    @24
    @14
    cS
    c.xp
    @40
    @2
    @23
    lclkrlem2m.q
    @44
    ringridm
    syl2anc
    3eqtrd
    oveq2d
    wph
    cS
    cgrp
    wcel
    #
    @18
    @37
    c.0
    wceq
    wph
    @17
    @45
    @20
    cS
    ringgrp
    syl
    @24
    @14
    cS
    @35
    @2
    c.0
    @23
    lclkrlem2m.z
    @38
    grpsubid
    syl2anc
    3eqtrd
    syl5eq
    jca
end
