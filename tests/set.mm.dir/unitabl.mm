include "ccrg.mm"
include "wcel.mm"
include "cgrp.mm"
include "ccmn.mm"
include "cabl.mm"
include "crg.mm"
include "crngring.mm"
include "unitgrp.mm"
include "syl.mm"
include "cmgp.mm"
include "cfv.mm"
include "cmnd.mm"
include "eqid.mm"
include "crngmgp.mm"
include "grpmnd.mm"
include "subcmn.mm"
include "syl2anc.mm"
include "isabl.mm"
include "sylanbrc.mm"

theorem unitabl
  let cR: class R
  let cU: class U
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vm: setvar m
  assume unitmulcl.1: |- U = ( Unit ` R )
  assume unitgrp.2: |- G = ( ( mulGrp ` R ) |`s U )


  assert |- ( R e. CRing -> G e. Abel )

  proof
    cR
    ccrg
    wcel
    #
    cG
    cgrp
    wcel
    #
    cG
    ccmn
    wcel
    #
    cG
    cabl
    wcel
    @0
    cR
    crg
    wcel
    @1
    cR
    crngring
    cR
    cU
    cG
    unitmulcl.1
    unitgrp.2
    unitgrp
    syl
    #
    @0
    cR
    cmgp
    cfv
    #
    ccmn
    wcel
    cG
    cmnd
    wcel
    #
    @2
    cR
    @4
    @4
    eqid
    crngmgp
    @0
    @1
    @5
    @3
    cG
    grpmnd
    syl
    cU
    @4
    cG
    unitgrp.2
    subcmn
    syl2anc
    cG
    isabl
    sylanbrc
end
