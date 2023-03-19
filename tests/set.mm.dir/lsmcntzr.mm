include "co.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "lsmcntz.mm"
include "cbs.mm"
include "wb.mm"
include "cmnd.mm"
include "wcel.mm"
include "csubg.mm"
include "cgrp.mm"
include "subgrcl.mm"
include "grpmnd.mm"
include "3syl.mm"
include "eqid.mm"
include "subgss.mm"
include "syl.mm"
include "lsmssv.mm"
include "syl3anc.mm"
include "cntzrec.mm"
include "syl2anc.mm"
include "anbi12d.mm"
include "3bitr3d.mm"

theorem lsmcntzr
  let wph: wff ph
  let c.po: class .(+)
  let cS: class S
  let cT: class T
  let cU: class U
  let cG: class G
  let cZ: class Z
  let vx: setvar x
  let vs: setvar s
  let vu: setvar u
  let c.0: class .0.
  assume lsmcntz.p: |- .(+) = ( LSSum ` G )
  assume lsmcntz.s: |- ( ph -> S e. ( SubGrp ` G ) )
  assume lsmcntz.t: |- ( ph -> T e. ( SubGrp ` G ) )
  assume lsmcntz.u: |- ( ph -> U e. ( SubGrp ` G ) )
  assume lsmcntz.z: |- Z = ( Cntz ` G )


  assert |- ( ph -> ( S C_ ( Z ` ( T .(+) U ) ) <-> ( S C_ ( Z ` T ) /\ S C_ ( Z ` U ) ) ) )

  proof
    wph
    cT
    cU
    c.po
    co
    #
    cS
    cZ
    cfv
    #
    wss
    #
    cT
    @1
    wss
    #
    cU
    @1
    wss
    #
    wa
    cS
    @0
    cZ
    cfv
    wss
    #
    cS
    cT
    cZ
    cfv
    wss
    #
    cS
    cU
    cZ
    cfv
    wss
    #
    wa
    wph
    c.po
    cT
    cU
    cS
    cG
    cZ
    lsmcntz.p
    lsmcntz.t
    lsmcntz.u
    lsmcntz.s
    lsmcntz.z
    lsmcntz
    wph
    @0
    cG
    cbs
    cfv
    #
    wss
    #
    cS
    @8
    wss
    #
    @2
    @5
    wb
    wph
    cG
    cmnd
    wcel
    #
    cT
    @8
    wss
    #
    cU
    @8
    wss
    #
    @9
    wph
    cS
    cG
    csubg
    cfv
    #
    wcel
    #
    cG
    cgrp
    wcel
    @11
    lsmcntz.s
    cS
    cG
    subgrcl
    cG
    grpmnd
    3syl
    wph
    cT
    @14
    wcel
    @12
    lsmcntz.t
    @8
    cT
    cG
    @8
    eqid
    #
    subgss
    syl
    #
    wph
    cU
    @14
    wcel
    @13
    lsmcntz.u
    @8
    cU
    cG
    @16
    subgss
    syl
    #
    @8
    c.po
    cT
    cU
    cG
    @16
    lsmcntz.p
    lsmssv
    syl3anc
    wph
    @15
    @10
    lsmcntz.s
    @8
    cS
    cG
    @16
    subgss
    syl
    #
    @8
    @0
    cS
    cG
    cZ
    @16
    lsmcntz.z
    cntzrec
    syl2anc
    wph
    @3
    @6
    @4
    @7
    wph
    @12
    @10
    @3
    @6
    wb
    @17
    @19
    @8
    cT
    cS
    cG
    cZ
    @16
    lsmcntz.z
    cntzrec
    syl2anc
    wph
    @13
    @10
    @4
    @7
    wb
    @18
    @19
    @8
    cU
    cS
    cG
    cZ
    @16
    lsmcntz.z
    cntzrec
    syl2anc
    anbi12d
    3bitr3d
end
