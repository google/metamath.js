include "cfv.mm"
include "wceq.mm"
include "csg.mm"
include "co.mm"
include "c0g.mm"
include "clcd.mm"
include "eqid.mm"
include "hdmapsub.mm"
include "eqeq1d.mm"
include "clmod.mm"
include "wcel.mm"
include "dvhlmod.mm"
include "lmodvsubcl.mm"
include "syl3anc.mm"
include "hdmapeq0.mm"
include "cgrp.mm"
include "cbs.mm"
include "wb.mm"
include "lcdlmod.mm"
include "lmodgrp.mm"
include "syl.mm"
include "hdmapcl.mm"
include "grpsubeq0.mm"
include "3bitr3rd.mm"
include "bitrd.mm"

theorem hdmap11
  let wph: wff ph
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume hdmap12d.h: |- H = ( LHyp ` K )
  assume hdmap12d.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmap12d.v: |- V = ( Base ` U )
  assume hdmap12d.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmap12d.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmap12d.x: |- ( ph -> X e. V )
  assume hdmap12d.y: |- ( ph -> Y e. V )


  assert |- ( ph -> ( ( S ` X ) = ( S ` Y ) <-> X = Y ) )

  proof
    wph
    cX
    cS
    cfv
    #
    cY
    cS
    cfv
    #
    wceq
    #
    cX
    cY
    cU
    csg
    cfv
    #
    co
    #
    cU
    c0g
    cfv
    #
    wceq
    #
    cX
    cY
    wceq
    #
    wph
    @4
    cS
    cfv
    #
    cW
    cK
    clcd
    cfv
    cfv
    #
    c0g
    cfv
    #
    wceq
    @0
    @1
    @9
    csg
    cfv
    #
    co
    #
    @10
    wceq
    #
    @6
    @2
    wph
    @8
    @12
    @10
    wph
    @9
    cS
    cU
    cH
    cK
    @3
    @11
    cV
    cW
    cX
    cY
    hdmap12d.h
    hdmap12d.u
    hdmap12d.v
    @3
    eqid
    #
    @9
    eqid
    #
    @11
    eqid
    #
    hdmap12d.s
    hdmap12d.k
    hdmap12d.x
    hdmap12d.y
    hdmapsub
    eqeq1d
    wph
    @9
    @10
    cS
    @4
    cU
    cH
    cK
    cV
    cW
    @5
    hdmap12d.h
    hdmap12d.u
    hdmap12d.v
    @5
    eqid
    #
    @15
    @10
    eqid
    #
    hdmap12d.s
    hdmap12d.k
    wph
    cU
    clmod
    wcel
    #
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    @4
    cV
    wcel
    wph
    cU
    cH
    cK
    cW
    hdmap12d.h
    hdmap12d.u
    hdmap12d.k
    dvhlmod
    #
    hdmap12d.x
    hdmap12d.y
    @3
    cV
    cU
    cX
    cY
    hdmap12d.v
    @14
    lmodvsubcl
    syl3anc
    hdmapeq0
    wph
    @9
    cgrp
    wcel
    #
    @0
    @9
    cbs
    cfv
    #
    wcel
    @1
    @24
    wcel
    @13
    @2
    wb
    wph
    @9
    clmod
    wcel
    @23
    wph
    @9
    cH
    cK
    cW
    hdmap12d.h
    @15
    hdmap12d.k
    lcdlmod
    @9
    lmodgrp
    syl
    wph
    @9
    @24
    cS
    cX
    cU
    cH
    cK
    cV
    cW
    hdmap12d.h
    hdmap12d.u
    hdmap12d.v
    @15
    @24
    eqid
    #
    hdmap12d.s
    hdmap12d.k
    hdmap12d.x
    hdmapcl
    wph
    @9
    @24
    cS
    cY
    cU
    cH
    cK
    cV
    cW
    hdmap12d.h
    hdmap12d.u
    hdmap12d.v
    @15
    @25
    hdmap12d.s
    hdmap12d.k
    hdmap12d.y
    hdmapcl
    @24
    @9
    @11
    @0
    @1
    @10
    @25
    @18
    @16
    grpsubeq0
    syl3anc
    3bitr3rd
    wph
    cU
    cgrp
    wcel
    #
    @20
    @21
    @6
    @7
    wb
    wph
    @19
    @26
    @22
    cU
    lmodgrp
    syl
    hdmap12d.x
    hdmap12d.y
    cV
    cU
    @3
    cX
    cY
    @5
    hdmap12d.v
    @17
    @14
    grpsubeq0
    syl3anc
    bitrd
end
