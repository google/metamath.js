include "co.mm"
include "csca.mm"
include "cfv.mm"
include "cur.mm"
include "cminusg.mm"
include "cvsca.mm"
include "cplusg.mm"
include "eqid.mm"
include "ldualvsub.mm"
include "cbs.mm"
include "cgrp.mm"
include "wcel.mm"
include "crg.mm"
include "clmod.mm"
include "lmodring.mm"
include "syl.mm"
include "ringgrp.mm"
include "ringidcl.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "ldualvscl.mm"
include "ldualvaddcl.mm"
include "eqeltrd.mm"

theorem ldualvsubcl
  let wph: wff ph
  let cD: class D
  let cF: class F
  let cG: class G
  let cH: class H
  let c.mi: class .-
  let cW: class W
  assume ldualvsubcl.f: |- F = ( LFnl ` W )
  assume ldualvsubcl.d: |- D = ( LDual ` W )
  assume ldualvsubcl.m: |- .- = ( -g ` D )
  assume ldualvsubcl.w: |- ( ph -> W e. LMod )
  assume ldualvsubcl.g: |- ( ph -> G e. F )
  assume ldualvsubcl.h: |- ( ph -> H e. F )


  assert |- ( ph -> ( G .- H ) e. F )

  proof
    wph
    cG
    cH
    c.mi
    co
    cG
    cW
    csca
    cfv
    #
    cur
    cfv
    #
    @0
    cminusg
    cfv
    #
    cfv
    #
    cH
    cD
    cvsca
    cfv
    #
    co
    #
    cD
    cplusg
    cfv
    #
    co
    cF
    wph
    cD
    @6
    @0
    @4
    @1
    cF
    cG
    cH
    c.mi
    @2
    cW
    @0
    eqid
    #
    @2
    eqid
    #
    @1
    eqid
    #
    ldualvsubcl.f
    ldualvsubcl.d
    @6
    eqid
    #
    @4
    eqid
    #
    ldualvsubcl.m
    ldualvsubcl.w
    ldualvsubcl.g
    ldualvsubcl.h
    ldualvsub
    wph
    cD
    @6
    cF
    cG
    @5
    cW
    ldualvsubcl.f
    ldualvsubcl.d
    @10
    ldualvsubcl.w
    ldualvsubcl.g
    wph
    cD
    @0
    @4
    cF
    cH
    @0
    cbs
    cfv
    #
    cW
    @3
    ldualvsubcl.f
    @7
    @12
    eqid
    #
    ldualvsubcl.d
    @11
    ldualvsubcl.w
    wph
    @0
    cgrp
    wcel
    #
    @1
    @12
    wcel
    #
    @3
    @12
    wcel
    wph
    @0
    crg
    wcel
    #
    @14
    wph
    cW
    clmod
    wcel
    @16
    ldualvsubcl.w
    @0
    cW
    @7
    lmodring
    syl
    #
    @0
    ringgrp
    syl
    wph
    @16
    @15
    @17
    @12
    @0
    @1
    @13
    @9
    ringidcl
    syl
    @12
    @0
    @2
    @1
    @13
    @8
    grpinvcl
    syl2anc
    ldualvsubcl.h
    ldualvscl
    ldualvaddcl
    eqeltrd
end
