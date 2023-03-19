include "csn.mm"
include "cxp.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cof.mm"
include "clfn.mm"
include "clmod.mm"
include "eqid.mm"
include "wcel.mm"
include "lfl0f.mm"
include "syl.mm"
include "ldualvadd.mm"
include "lfladd0l.mm"
include "eqtrd.mm"
include "cgrp.mm"
include "cbs.mm"
include "wb.mm"
include "ldualgrp.mm"
include "ldualelvbase.mm"
include "grpid.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem ldual0v
  let wph: wff ph
  let cD: class D
  let cR: class R
  let cO: class O
  let cV: class V
  let cW: class W
  let c.0: class .0.
  assume ldualv0.v: |- V = ( Base ` W )
  assume ldualv0.r: |- R = ( Scalar ` W )
  assume ldualv0.z: |- .0. = ( 0g ` R )
  assume ldualv0.d: |- D = ( LDual ` W )
  assume ldualv0.o: |- O = ( 0g ` D )
  assume ldualv0.w: |- ( ph -> W e. LMod )


  assert |- ( ph -> O = ( V X. { .0. } ) )

  proof
    wph
    cV
    c.0
    csn
    cxp
    #
    @0
    cD
    cplusg
    cfv
    #
    co
    #
    @0
    wceq
    #
    cO
    @0
    wceq
    #
    wph
    @2
    @0
    @0
    cR
    cplusg
    cfv
    #
    cof
    co
    @0
    wph
    cD
    @5
    @1
    cR
    cW
    clfn
    cfv
    #
    @0
    @0
    cW
    clmod
    @6
    eqid
    #
    ldualv0.r
    @5
    eqid
    #
    ldualv0.d
    @1
    eqid
    #
    ldualv0.w
    wph
    cW
    clmod
    wcel
    @0
    @6
    wcel
    ldualv0.w
    cR
    @6
    cV
    cW
    c.0
    ldualv0.r
    ldualv0.z
    ldualv0.v
    @7
    lfl0f
    syl
    #
    @10
    ldualvadd
    wph
    @5
    cR
    @6
    @0
    cV
    cW
    c.0
    ldualv0.v
    ldualv0.r
    @8
    ldualv0.z
    @7
    ldualv0.w
    @10
    lfladd0l
    eqtrd
    wph
    cD
    cgrp
    wcel
    @0
    cD
    cbs
    cfv
    #
    wcel
    @3
    @4
    wb
    wph
    cD
    cW
    ldualv0.d
    ldualv0.w
    ldualgrp
    wph
    cD
    @6
    @0
    @11
    cW
    clmod
    @7
    ldualv0.d
    @11
    eqid
    #
    ldualv0.w
    @10
    ldualelvbase
    @11
    @1
    cD
    @0
    cO
    @12
    @9
    ldualv0.o
    grpid
    syl2anc
    mpbid
end
