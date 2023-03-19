include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cid.mm"
include "cbs.mm"
include "cfv.mm"
include "cres.mm"
include "wne.mm"
include "cdr.mm"
include "cltrn.mm"
include "eqid.mm"
include "cdlemftr0.mm"
include "ctendo.mm"
include "ccom.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "coc.mm"
include "ctrl.mm"
include "wceq.mm"
include "w3a.mm"
include "cjn.mm"
include "co.mm"
include "ccnv.mm"
include "cmee.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "cif.mm"
include "erngdvlem4.mm"
include "rexlimddv.mm"

theorem erngdv
  let cD: class D
  let cH: class H
  let cK: class K
  let cW: class W
  let cB: class B
  let vf: setvar f
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let va: setvar a
  let vb: setvar b
  let cE: class E
  let cI: class I
  let c.0: class .0.
  let cT: class T
  let cP: class P
  let vg: setvar g
  let vz: setvar z
  assume ernggrp.h: |- H = ( LHyp ` K )
  assume ernggrp.d: |- D = ( ( EDRing ` K ) ` W )


  assert |- ( ( K e. HL /\ W e. H ) -> D e. DivRing )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    vf
    cv
    #
    cid
    cK
    cbs
    cfv
    #
    cres
    #
    wne
    cD
    cdr
    wcel
    vf
    cW
    cK
    cltrn
    cfv
    cfv
    #
    @1
    @3
    vf
    cH
    cK
    cW
    @1
    eqid
    #
    ernggrp.h
    @3
    eqid
    #
    cdlemftr0
    vz
    @1
    cD
    va
    vb
    cW
    cK
    ctendo
    cfv
    cfv
    #
    @6
    vf
    @3
    @0
    va
    cv
    #
    cfv
    #
    @0
    vb
    cv
    #
    cfv
    ccom
    cmpt
    cmpt2
    #
    va
    vb
    @6
    @6
    @7
    @9
    ccom
    cmpt2
    #
    cW
    cK
    coc
    cfv
    cfv
    #
    cW
    cK
    ctrl
    cfv
    cfv
    #
    @3
    vg
    @3
    @0
    vs
    cv
    cfv
    #
    @0
    wceq
    vg
    cv
    #
    @9
    @2
    wne
    @9
    @13
    cfv
    #
    @14
    @13
    cfv
    wne
    @16
    @15
    @13
    cfv
    #
    wne
    w3a
    @12
    vz
    cv
    cfv
    @12
    @17
    cK
    cjn
    cfv
    #
    co
    @12
    @16
    @18
    co
    @12
    @0
    cfv
    @9
    @14
    ccnv
    ccom
    @13
    cfv
    @18
    co
    cK
    cmee
    cfv
    #
    co
    #
    @15
    @9
    ccnv
    ccom
    @13
    cfv
    @18
    co
    @19
    co
    #
    wceq
    wi
    vb
    @3
    wral
    vz
    @3
    crio
    #
    cif
    cmpt
    #
    vf
    vg
    vf
    @6
    cH
    va
    @6
    vf
    @3
    @8
    ccnv
    cmpt
    cmpt
    #
    @18
    cK
    @19
    cW
    @22
    @21
    vf
    @3
    @2
    cmpt
    #
    @20
    vs
    va
    vb
    ernggrp.h
    ernggrp.d
    @4
    @5
    @6
    eqid
    @10
    eqid
    @25
    eqid
    @24
    eqid
    @11
    eqid
    @18
    eqid
    @19
    eqid
    @13
    eqid
    @12
    eqid
    @20
    eqid
    @21
    eqid
    @22
    eqid
    @23
    eqid
    erngdvlem4
    rexlimddv
end
