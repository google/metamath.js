include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "co.mm"
include "csubg.mm"
include "wcel.mm"
include "wb.mm"
include "cgrp.mm"
include "cbs.mm"
include "subgrcl.mm"
include "eqid.mm"
include "subgss.mm"
include "cntzsubg.mm"
include "syl2anc.mm"
include "syl.mm"
include "lsmlub.mm"
include "syl3anc.mm"
include "bicomd.mm"

theorem lsmcntz
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


  assert |- ( ph -> ( ( S .(+) T ) C_ ( Z ` U ) <-> ( S C_ ( Z ` U ) /\ T C_ ( Z ` U ) ) ) )

  proof
    wph
    cS
    cU
    cZ
    cfv
    #
    wss
    cT
    @0
    wss
    wa
    #
    cS
    cT
    c.po
    co
    @0
    wss
    #
    wph
    cS
    cG
    csubg
    cfv
    #
    wcel
    cT
    @3
    wcel
    @0
    @3
    wcel
    #
    @1
    @2
    wb
    lsmcntz.s
    lsmcntz.t
    wph
    cU
    @3
    wcel
    #
    @4
    lsmcntz.u
    @5
    cG
    cgrp
    wcel
    cU
    cG
    cbs
    cfv
    #
    wss
    @4
    cU
    cG
    subgrcl
    @6
    cU
    cG
    @6
    eqid
    #
    subgss
    @6
    cU
    cG
    cZ
    @7
    lsmcntz.z
    cntzsubg
    syl2anc
    syl
    c.po
    cS
    cT
    @0
    cG
    lsmcntz.p
    lsmlub
    syl3anc
    bicomd
end
