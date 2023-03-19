include "co.mm"
include "wf.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "crio.mm"
include "cmpt.mm"
include "wcel.mm"
include "wa.mm"
include "wreu.mm"
include "pj1eu.mm"
include "riotacl.mm"
include "syl.mm"
include "eqid.mm"
include "fmptd.mm"
include "cgrp.mm"
include "cbs.mm"
include "cfv.mm"
include "wss.mm"
include "csubg.mm"
include "subgrcl.mm"
include "subgss.mm"
include "pj1fval.mm"
include "syl3anc.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem pj1f
  let wph: wff ph
  let cP: class P
  let c.pl: class .+
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let cG: class G
  let c.0: class .0.
  let cZ: class Z
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cX: class X
  assume pj1eu.a: |- .+ = ( +g ` G )
  assume pj1eu.s: |- .(+) = ( LSSum ` G )
  assume pj1eu.o: |- .0. = ( 0g ` G )
  assume pj1eu.z: |- Z = ( Cntz ` G )
  assume pj1eu.2: |- ( ph -> T e. ( SubGrp ` G ) )
  assume pj1eu.3: |- ( ph -> U e. ( SubGrp ` G ) )
  assume pj1eu.4: |- ( ph -> ( T i^i U ) = { .0. } )
  assume pj1eu.5: |- ( ph -> T C_ ( Z ` U ) )
  assume pj1f.p: |- P = ( proj1 ` G )


  assert |- ( ph -> ( T P U ) : ( T .(+) U ) --> T )

  proof
    wph
    cT
    cU
    c.po
    co
    #
    cT
    cT
    cU
    cP
    co
    #
    wf
    @0
    cT
    vz
    @0
    vz
    cv
    #
    vx
    cv
    vy
    cv
    c.pl
    co
    wceq
    vy
    cU
    wrex
    #
    vx
    cT
    crio
    #
    cmpt
    #
    wf
    wph
    vz
    @0
    @4
    cT
    @5
    wph
    @2
    @0
    wcel
    wa
    @3
    vx
    cT
    wreu
    @4
    cT
    wcel
    wph
    vx
    vy
    c.pl
    c.po
    cT
    cU
    cG
    @2
    c.0
    cZ
    pj1eu.a
    pj1eu.s
    pj1eu.o
    pj1eu.z
    pj1eu.2
    pj1eu.3
    pj1eu.4
    pj1eu.5
    pj1eu
    @3
    vx
    cT
    riotacl
    syl
    @5
    eqid
    fmptd
    wph
    @0
    cT
    @1
    @5
    wph
    cG
    cgrp
    wcel
    #
    cT
    cG
    cbs
    cfv
    #
    wss
    #
    cU
    @7
    wss
    #
    @1
    @5
    wceq
    wph
    cT
    cG
    csubg
    cfv
    #
    wcel
    #
    @6
    pj1eu.2
    cT
    cG
    subgrcl
    syl
    wph
    @11
    @8
    pj1eu.2
    @7
    cT
    cG
    @7
    eqid
    #
    subgss
    syl
    wph
    cU
    @10
    wcel
    @9
    pj1eu.3
    @7
    cU
    cG
    @12
    subgss
    syl
    vx
    vy
    vz
    @7
    cP
    c.pl
    c.po
    cT
    cU
    cG
    cgrp
    @12
    pj1eu.a
    pj1eu.s
    pj1f.p
    pj1fval
    syl3anc
    feq1d
    mpbird
end
