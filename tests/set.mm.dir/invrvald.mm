include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "cdsr.mm"
include "wbr.mm"
include "coppr.mm"
include "co.mm"
include "eqid.mm"
include "dvdsrmul.mm"
include "syl2anc.mm"
include "breqtrd.mm"
include "cmulr.mm"
include "opprbas.mm"
include "opprmul.mm"
include "syl5eq.mm"
include "isunit.mm"
include "sylanbrc.mm"
include "cmgp.mm"
include "cress.mm"
include "c0g.mm"
include "crg.mm"
include "unitgrpid.mm"
include "syl.mm"
include "eqtrd.mm"
include "cgrp.mm"
include "wb.mm"
include "unitgrp.mm"
include "unitgrpbas.mm"
include "cvv.mm"
include "cplusg.mm"
include "cui.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mgpplusg.mm"
include "ressplusg.mm"
include "ax-mp.mm"
include "invrfval.mm"
include "grpinvid1.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "jca.mm"

theorem invrvald
  let wph: wff ph
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let c.1: class .1.
  let cI: class I
  let cX: class X
  let cY: class Y
  assume invrvald.b: |- B = ( Base ` R )
  assume invrvald.t: |- .x. = ( .r ` R )
  assume invrvald.o: |- .1. = ( 1r ` R )
  assume invrvald.u: |- U = ( Unit ` R )
  assume invrvald.i: |- I = ( invr ` R )
  assume invrvald.r: |- ( ph -> R e. Ring )
  assume invrvald.x: |- ( ph -> X e. B )
  assume invrvald.y: |- ( ph -> Y e. B )
  assume invrvald.xy: |- ( ph -> ( X .x. Y ) = .1. )
  assume invrvald.yx: |- ( ph -> ( Y .x. X ) = .1. )


  assert |- ( ph -> ( X e. U /\ ( I ` X ) = Y ) )

  proof
    wph
    cX
    cU
    wcel
    #
    cX
    cI
    cfv
    cY
    wceq
    #
    wph
    cX
    c.1
    cR
    cdsr
    cfv
    #
    wbr
    cX
    c.1
    cR
    coppr
    cfv
    #
    cdsr
    cfv
    #
    wbr
    @0
    wph
    cX
    cY
    cX
    c.x
    co
    #
    c.1
    @2
    wph
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    cX
    @5
    @2
    wbr
    invrvald.x
    invrvald.y
    cB
    @2
    cR
    c.x
    cX
    cY
    invrvald.b
    @2
    eqid
    #
    invrvald.t
    dvdsrmul
    syl2anc
    invrvald.yx
    breqtrd
    wph
    cX
    cY
    cX
    @3
    cmulr
    cfv
    #
    co
    #
    c.1
    @4
    wph
    @6
    @7
    cX
    @10
    @4
    wbr
    invrvald.x
    invrvald.y
    cB
    @4
    @3
    @9
    cX
    cY
    cB
    cR
    @3
    @3
    eqid
    #
    invrvald.b
    opprbas
    #
    @4
    eqid
    #
    @9
    eqid
    #
    dvdsrmul
    syl2anc
    wph
    @10
    cX
    cY
    c.x
    co
    #
    c.1
    cB
    cR
    @9
    c.x
    @3
    cY
    cX
    invrvald.b
    invrvald.t
    @11
    @14
    opprmul
    invrvald.xy
    syl5eq
    breqtrd
    @2
    cR
    @3
    cU
    c.1
    @4
    cX
    invrvald.u
    invrvald.o
    @8
    @11
    @13
    isunit
    sylanbrc
    #
    wph
    @1
    @15
    cR
    cmgp
    cfv
    #
    cU
    cress
    co
    #
    c0g
    cfv
    #
    wceq
    #
    wph
    @15
    c.1
    @19
    invrvald.xy
    wph
    cR
    crg
    wcel
    #
    c.1
    @19
    wceq
    invrvald.r
    cR
    cU
    c.1
    @18
    invrvald.u
    @18
    eqid
    #
    invrvald.o
    unitgrpid
    syl
    eqtrd
    wph
    @18
    cgrp
    wcel
    #
    @0
    cY
    cU
    wcel
    #
    @1
    @20
    wb
    wph
    @21
    @23
    invrvald.r
    cR
    cU
    @18
    invrvald.u
    @22
    unitgrp
    syl
    @16
    wph
    cY
    c.1
    @2
    wbr
    cY
    c.1
    @4
    wbr
    @24
    wph
    cY
    @15
    c.1
    @2
    wph
    @7
    @6
    cY
    @15
    @2
    wbr
    invrvald.y
    invrvald.x
    cB
    @2
    cR
    c.x
    cY
    cX
    invrvald.b
    @8
    invrvald.t
    dvdsrmul
    syl2anc
    invrvald.xy
    breqtrd
    wph
    cY
    cX
    cY
    @9
    co
    #
    c.1
    @4
    wph
    @7
    @6
    cY
    @25
    @4
    wbr
    invrvald.y
    invrvald.x
    cB
    @4
    @3
    @9
    cY
    cX
    @12
    @13
    @14
    dvdsrmul
    syl2anc
    wph
    @25
    @5
    c.1
    cB
    cR
    @9
    c.x
    @3
    cX
    cY
    invrvald.b
    invrvald.t
    @11
    @14
    opprmul
    invrvald.yx
    syl5eq
    breqtrd
    @2
    cR
    @3
    cU
    c.1
    @4
    cY
    invrvald.u
    invrvald.o
    @8
    @11
    @13
    isunit
    sylanbrc
    cU
    c.x
    @18
    cI
    cX
    cY
    @19
    cR
    cU
    @18
    invrvald.u
    @22
    unitgrpbas
    cU
    cvv
    wcel
    c.x
    @18
    cplusg
    cfv
    wceq
    cU
    cR
    cui
    cfv
    cvv
    invrvald.u
    cR
    cui
    fvex
    eqeltri
    cU
    c.x
    @17
    @18
    cvv
    @22
    cR
    c.x
    @17
    @17
    eqid
    invrvald.t
    mgpplusg
    ressplusg
    ax-mp
    @19
    eqid
    cR
    cU
    @18
    cI
    invrvald.u
    @22
    invrvald.i
    invrfval
    grpinvid1
    syl3anc
    mpbird
    jca
end
