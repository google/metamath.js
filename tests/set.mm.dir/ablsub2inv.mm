include "cfv.mm"
include "co.mm"
include "cplusg.mm"
include "eqid.mm"
include "cabl.mm"
include "wcel.mm"
include "cgrp.mm"
include "ablgrp.mm"
include "syl.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "grpsubinv.mm"
include "wceq.mm"
include "ablcom.mm"
include "syl3anc.mm"
include "grpinvinv.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "grpinvadd.mm"
include "grpsubval.mm"
include "fveq2d.mm"
include "grpinvsub.mm"
include "3eqtrd.mm"

theorem ablsub2inv
  let wph: wff ph
  let cB: class B
  let cG: class G
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let cY: class Y
  assume ablsub2inv.b: |- B = ( Base ` G )
  assume ablsub2inv.m: |- .- = ( -g ` G )
  assume ablsub2inv.n: |- N = ( invg ` G )
  assume ablsub2inv.g: |- ( ph -> G e. Abel )
  assume ablsub2inv.x: |- ( ph -> X e. B )
  assume ablsub2inv.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( ( N ` X ) .- ( N ` Y ) ) = ( Y .- X ) )

  proof
    wph
    cX
    cN
    cfv
    #
    cY
    cN
    cfv
    #
    c.mi
    co
    @0
    cY
    cG
    cplusg
    cfv
    #
    co
    #
    cX
    cY
    c.mi
    co
    #
    cN
    cfv
    #
    cY
    cX
    c.mi
    co
    #
    wph
    cB
    @2
    cG
    c.mi
    cN
    @0
    cY
    ablsub2inv.b
    @2
    eqid
    #
    ablsub2inv.m
    ablsub2inv.n
    wph
    cG
    cabl
    wcel
    #
    cG
    cgrp
    wcel
    #
    ablsub2inv.g
    cG
    ablgrp
    syl
    #
    wph
    @9
    cX
    cB
    wcel
    #
    @0
    cB
    wcel
    #
    @10
    ablsub2inv.x
    cB
    cG
    cN
    cX
    ablsub2inv.b
    ablsub2inv.n
    grpinvcl
    syl2anc
    #
    ablsub2inv.y
    grpsubinv
    wph
    @3
    cX
    @1
    @2
    co
    #
    cN
    cfv
    #
    @5
    wph
    @3
    @1
    cN
    cfv
    #
    @0
    @2
    co
    #
    @15
    wph
    @3
    cY
    @0
    @2
    co
    #
    @17
    wph
    @8
    @12
    cY
    cB
    wcel
    #
    @3
    @18
    wceq
    ablsub2inv.g
    @13
    ablsub2inv.y
    cB
    @2
    cG
    @0
    cY
    ablsub2inv.b
    @7
    ablcom
    syl3anc
    wph
    @16
    cY
    @0
    @2
    wph
    @9
    @19
    @16
    cY
    wceq
    @10
    ablsub2inv.y
    cB
    cG
    cN
    cY
    ablsub2inv.b
    ablsub2inv.n
    grpinvinv
    syl2anc
    oveq1d
    eqtr4d
    wph
    @9
    @11
    @1
    cB
    wcel
    #
    @15
    @17
    wceq
    @10
    ablsub2inv.x
    wph
    @9
    @19
    @20
    @10
    ablsub2inv.y
    cB
    cG
    cN
    cY
    ablsub2inv.b
    ablsub2inv.n
    grpinvcl
    syl2anc
    cB
    @2
    cG
    cN
    cX
    @1
    ablsub2inv.b
    @7
    ablsub2inv.n
    grpinvadd
    syl3anc
    eqtr4d
    wph
    @4
    @14
    cN
    wph
    @11
    @19
    @4
    @14
    wceq
    ablsub2inv.x
    ablsub2inv.y
    cB
    @2
    cG
    cN
    c.mi
    cX
    cY
    ablsub2inv.b
    @7
    ablsub2inv.n
    ablsub2inv.m
    grpsubval
    syl2anc
    fveq2d
    eqtr4d
    wph
    @9
    @11
    @19
    @5
    @6
    wceq
    @10
    ablsub2inv.x
    ablsub2inv.y
    cB
    cG
    c.mi
    cN
    cX
    cY
    ablsub2inv.b
    ablsub2inv.m
    ablsub2inv.n
    grpinvsub
    syl3anc
    3eqtrd
end
