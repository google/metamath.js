include "co.mm"
include "wbr.mm"
include "cple.mm"
include "cfv.mm"
include "wne.mm"
include "corng.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "crg.mm"
include "cgrp.mm"
include "orngring.mm"
include "ringgrp.mm"
include "grpidcl.mm"
include "4syl.mm"
include "eqid.mm"
include "pltval.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "simpld.mm"
include "orngmul.mm"
include "syl122anc.mm"
include "simprd.mm"
include "necomd.mm"
include "drngmulne0.mm"
include "mpbir2and.mm"
include "syl.mm"
include "ringcl.mm"

theorem orngmullt
  let wph: wff ph
  let cB: class B
  let cR: class R
  let c.lt: class .<
  let c.x: class .x.
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume orngmullt.b: |- B = ( Base ` R )
  assume orngmullt.t: |- .x. = ( .r ` R )
  assume orngmullt.0: |- .0. = ( 0g ` R )
  assume orngmullt.l: |- .< = ( lt ` R )
  assume orngmullt.1: |- ( ph -> R e. oRing )
  assume orngmullt.4: |- ( ph -> R e. DivRing )
  assume orngmullt.2: |- ( ph -> X e. B )
  assume orngmullt.3: |- ( ph -> Y e. B )
  assume orngmullt.x: |- ( ph -> .0. .< X )
  assume orngmullt.y: |- ( ph -> .0. .< Y )


  assert |- ( ph -> .0. .< ( X .x. Y ) )

  proof
    wph
    c.0
    cX
    cY
    c.x
    co
    #
    c.lt
    wbr
    #
    c.0
    @0
    cR
    cple
    cfv
    #
    wbr
    #
    c.0
    @0
    wne
    #
    wph
    cR
    corng
    wcel
    #
    cX
    cB
    wcel
    #
    c.0
    cX
    @2
    wbr
    #
    cY
    cB
    wcel
    #
    c.0
    cY
    @2
    wbr
    #
    @3
    orngmullt.1
    orngmullt.2
    wph
    @7
    c.0
    cX
    wne
    #
    wph
    c.0
    cX
    c.lt
    wbr
    #
    @7
    @10
    wa
    #
    orngmullt.x
    wph
    @5
    c.0
    cB
    wcel
    #
    @6
    @11
    @12
    wb
    orngmullt.1
    wph
    @5
    cR
    crg
    wcel
    #
    cR
    cgrp
    wcel
    @13
    orngmullt.1
    cR
    orngring
    #
    cR
    ringgrp
    cB
    cR
    c.0
    orngmullt.b
    orngmullt.0
    grpidcl
    4syl
    #
    orngmullt.2
    corng
    cB
    cB
    c.lt
    cR
    @2
    c.0
    cX
    @2
    eqid
    #
    orngmullt.l
    pltval
    syl3anc
    mpbid
    #
    simpld
    orngmullt.3
    wph
    @9
    c.0
    cY
    wne
    #
    wph
    c.0
    cY
    c.lt
    wbr
    #
    @9
    @19
    wa
    #
    orngmullt.y
    wph
    @5
    @13
    @8
    @20
    @21
    wb
    orngmullt.1
    @16
    orngmullt.3
    corng
    cB
    cB
    c.lt
    cR
    @2
    c.0
    cY
    @17
    orngmullt.l
    pltval
    syl3anc
    mpbid
    #
    simpld
    cB
    cR
    c.x
    @2
    cX
    cY
    c.0
    orngmullt.b
    @17
    orngmullt.0
    orngmullt.t
    orngmul
    syl122anc
    wph
    @0
    c.0
    wph
    @0
    c.0
    wne
    cX
    c.0
    wne
    cY
    c.0
    wne
    wph
    c.0
    cX
    wph
    @7
    @10
    @18
    simprd
    necomd
    wph
    c.0
    cY
    wph
    @9
    @19
    @22
    simprd
    necomd
    wph
    cB
    cR
    c.x
    cX
    cY
    c.0
    orngmullt.b
    orngmullt.0
    orngmullt.t
    orngmullt.4
    orngmullt.2
    orngmullt.3
    drngmulne0
    mpbir2and
    necomd
    wph
    @5
    @13
    @0
    cB
    wcel
    #
    @1
    @3
    @4
    wa
    wb
    orngmullt.1
    @16
    wph
    @14
    @6
    @8
    @23
    wph
    @5
    @14
    orngmullt.1
    @15
    syl
    orngmullt.2
    orngmullt.3
    cB
    cR
    c.x
    cX
    cY
    orngmullt.b
    orngmullt.t
    ringcl
    syl3anc
    corng
    cB
    cB
    c.lt
    cR
    @2
    c.0
    @0
    @17
    orngmullt.l
    pltval
    syl3anc
    mpbir2and
end
