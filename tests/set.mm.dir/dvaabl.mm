include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cltrn.mm"
include "cop.mm"
include "cplusg.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt2.mm"
include "csca.mm"
include "cedring.mm"
include "ctp.mm"
include "cvsca.mm"
include "ctendo.mm"
include "csn.mm"
include "cun.mm"
include "cabl.mm"
include "eqid.mm"
include "dvaset.mm"
include "cpr.mm"
include "ctgrp.mm"
include "tgrpset.mm"
include "tgrpabl.mm"
include "eqeltrrd.mm"
include "cvv.mm"
include "wceq.mm"
include "fvex.mm"
include "grpbase.mm"
include "lmodbase.mm"
include "eqtr3d.mm"
include "ax-mp.mm"
include "mpt2ex.mm"
include "grpplusg.mm"
include "lmodplusg.mm"
include "ablprop.mm"
include "sylib.mm"
include "eqeltrd.mm"

theorem dvaabl
  let cU: class U
  let cH: class H
  let cK: class K
  let cW: class W
  let vf: setvar f
  let vt: setvar t
  let c.pd: class .+^
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vs: setvar s
  let cE: class E
  let vg: setvar g
  let c.pl: class .+
  let cT: class T
  let c.x: class .x.
  let c.xp: class .X.
  assume dvalvec.h: |- H = ( LHyp ` K )
  assume dvalvec.v: |- U = ( ( DVecA ` K ) ` W )


  assert |- ( ( K e. HL /\ W e. H ) -> U e. Abel )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cU
    cnx
    cbs
    cfv
    cW
    cK
    cltrn
    cfv
    #
    cfv
    #
    cop
    #
    cnx
    cplusg
    cfv
    vf
    vg
    @2
    @2
    vf
    cv
    #
    vg
    cv
    ccom
    #
    cmpt2
    #
    cop
    #
    cnx
    csca
    cfv
    cW
    cK
    cedring
    cfv
    cfv
    #
    cop
    ctp
    cnx
    cvsca
    cfv
    vs
    vf
    cW
    cK
    ctendo
    cfv
    cfv
    #
    @2
    @4
    vs
    cv
    cfv
    cmpt2
    #
    cop
    csn
    cun
    #
    cabl
    @8
    @2
    cU
    vf
    vg
    @9
    cH
    cK
    cW
    chlt
    vs
    dvalvec.h
    @2
    eqid
    #
    @9
    eqid
    @8
    eqid
    dvalvec.v
    dvaset
    @0
    @3
    @7
    cpr
    #
    cabl
    wcel
    @11
    cabl
    wcel
    @0
    cW
    cK
    ctgrp
    cfv
    cfv
    #
    @13
    cabl
    @2
    vf
    vg
    @14
    cH
    cK
    chlt
    cW
    dvalvec.h
    @12
    @14
    eqid
    #
    tgrpset
    @14
    cH
    cK
    cW
    dvalvec.h
    @15
    tgrpabl
    eqeltrrd
    @13
    @11
    @2
    cvv
    wcel
    #
    @13
    cbs
    cfv
    #
    @11
    cbs
    cfv
    #
    wceq
    cW
    @1
    fvex
    #
    @16
    @2
    @17
    @18
    @2
    @6
    @13
    cvv
    @13
    eqid
    #
    grpbase
    @2
    @6
    @10
    @8
    @11
    cvv
    @11
    eqid
    #
    lmodbase
    eqtr3d
    ax-mp
    @6
    cvv
    wcel
    #
    @13
    cplusg
    cfv
    #
    @11
    cplusg
    cfv
    #
    wceq
    vf
    vg
    @2
    @2
    @5
    @19
    @19
    mpt2ex
    @22
    @6
    @23
    @24
    @2
    @6
    @13
    cvv
    @20
    grpplusg
    @2
    @6
    @10
    @8
    @11
    cvv
    @21
    lmodplusg
    eqtr3d
    ax-mp
    ablprop
    sylib
    eqeltrd
end
