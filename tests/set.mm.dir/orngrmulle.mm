include "co.mm"
include "cplusg.mm"
include "cfv.mm"
include "csg.mm"
include "comnd.mm"
include "wcel.mm"
include "wbr.mm"
include "cogrp.mm"
include "corng.mm"
include "orngogrp.mm"
include "syl.mm"
include "cgrp.mm"
include "isogrp.mm"
include "simprbi.mm"
include "crg.mm"
include "orngring.mm"
include "ringgrp.mm"
include "grpidcl.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "eqid.mm"
include "grpsubcl.mm"
include "wceq.mm"
include "grpsubid.mm"
include "syl2anc.mm"
include "ogrpsub.mm"
include "syl131anc.mm"
include "eqbrtrrd.mm"
include "orngmul.mm"
include "syl122anc.mm"
include "rngsubdir.mm"
include "breqtrd.mm"
include "omndadd.mm"
include "grplid.mm"
include "grpnpcan.mm"
include "3brtr3d.mm"

theorem orngrmulle
  let wph: wff ph
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  assume ornglmullt.b: |- B = ( Base ` R )
  assume ornglmullt.t: |- .x. = ( .r ` R )
  assume ornglmullt.0: |- .0. = ( 0g ` R )
  assume ornglmullt.1: |- ( ph -> R e. oRing )
  assume ornglmullt.2: |- ( ph -> X e. B )
  assume ornglmullt.3: |- ( ph -> Y e. B )
  assume ornglmullt.4: |- ( ph -> Z e. B )
  assume orngmulle.l: |- .<_ = ( le ` R )
  assume orngmulle.5: |- ( ph -> X .<_ Y )
  assume orngmulle.6: |- ( ph -> .0. .<_ Z )


  assert |- ( ph -> ( X .x. Z ) .<_ ( Y .x. Z ) )

  proof
    wph
    c.0
    cX
    cZ
    c.x
    co
    #
    cR
    cplusg
    cfv
    #
    co
    #
    cY
    cZ
    c.x
    co
    #
    @0
    cR
    csg
    cfv
    #
    co
    #
    @0
    @1
    co
    #
    @0
    @3
    c.le
    wph
    cR
    comnd
    wcel
    #
    c.0
    cB
    wcel
    #
    @5
    cB
    wcel
    #
    @0
    cB
    wcel
    #
    c.0
    @5
    c.le
    wbr
    @2
    @6
    c.le
    wbr
    wph
    cR
    cogrp
    wcel
    #
    @7
    wph
    cR
    corng
    wcel
    #
    @11
    ornglmullt.1
    cR
    orngogrp
    syl
    #
    @11
    cR
    cgrp
    wcel
    #
    @7
    cR
    isogrp
    simprbi
    syl
    wph
    @14
    @8
    wph
    cR
    crg
    wcel
    #
    @14
    wph
    @12
    @15
    ornglmullt.1
    cR
    orngring
    syl
    #
    cR
    ringgrp
    syl
    #
    cB
    cR
    c.0
    ornglmullt.b
    ornglmullt.0
    grpidcl
    syl
    wph
    @14
    @3
    cB
    wcel
    #
    @10
    @9
    @17
    wph
    @15
    cY
    cB
    wcel
    #
    cZ
    cB
    wcel
    #
    @18
    @16
    ornglmullt.3
    ornglmullt.4
    cB
    cR
    c.x
    cY
    cZ
    ornglmullt.b
    ornglmullt.t
    ringcl
    syl3anc
    #
    wph
    @15
    cX
    cB
    wcel
    #
    @20
    @10
    @16
    ornglmullt.2
    ornglmullt.4
    cB
    cR
    c.x
    cX
    cZ
    ornglmullt.b
    ornglmullt.t
    ringcl
    syl3anc
    #
    cB
    cR
    @4
    @3
    @0
    ornglmullt.b
    @4
    eqid
    #
    grpsubcl
    syl3anc
    @23
    wph
    c.0
    cY
    cX
    @4
    co
    #
    cZ
    c.x
    co
    #
    @5
    c.le
    wph
    @12
    @25
    cB
    wcel
    #
    c.0
    @25
    c.le
    wbr
    @20
    c.0
    cZ
    c.le
    wbr
    c.0
    @26
    c.le
    wbr
    ornglmullt.1
    wph
    @14
    @19
    @22
    @27
    @17
    ornglmullt.3
    ornglmullt.2
    cB
    cR
    @4
    cY
    cX
    ornglmullt.b
    @24
    grpsubcl
    syl3anc
    wph
    cX
    cX
    @4
    co
    #
    c.0
    @25
    c.le
    wph
    @14
    @22
    @28
    c.0
    wceq
    @17
    ornglmullt.2
    cB
    cR
    @4
    cX
    c.0
    ornglmullt.b
    ornglmullt.0
    @24
    grpsubid
    syl2anc
    wph
    @11
    @22
    @19
    @22
    cX
    cY
    c.le
    wbr
    @28
    @25
    c.le
    wbr
    @13
    ornglmullt.2
    ornglmullt.3
    ornglmullt.2
    orngmulle.5
    cB
    cR
    c.le
    @4
    cX
    cY
    cX
    ornglmullt.b
    orngmulle.l
    @24
    ogrpsub
    syl131anc
    eqbrtrrd
    ornglmullt.4
    orngmulle.6
    cB
    cR
    c.x
    c.le
    @25
    cZ
    c.0
    ornglmullt.b
    orngmulle.l
    ornglmullt.0
    ornglmullt.t
    orngmul
    syl122anc
    wph
    cB
    cR
    c.x
    @4
    cY
    cX
    cZ
    ornglmullt.b
    ornglmullt.t
    @24
    @16
    ornglmullt.3
    ornglmullt.2
    ornglmullt.4
    rngsubdir
    breqtrd
    cB
    @1
    c.le
    cR
    c.0
    @5
    @0
    ornglmullt.b
    orngmulle.l
    @1
    eqid
    #
    omndadd
    syl131anc
    wph
    @14
    @10
    @2
    @0
    wceq
    @17
    @23
    cB
    @1
    cR
    @0
    c.0
    ornglmullt.b
    @29
    ornglmullt.0
    grplid
    syl2anc
    wph
    @14
    @18
    @10
    @6
    @3
    wceq
    @17
    @21
    @23
    cB
    @1
    cR
    @4
    @3
    @0
    ornglmullt.b
    @29
    @24
    grpnpcan
    syl3anc
    3brtr3d
end
