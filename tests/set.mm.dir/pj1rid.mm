include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "cgrp.mm"
include "cbs.mm"
include "csubg.mm"
include "adantr.mm"
include "subgrcl.mm"
include "syl.mm"
include "wss.mm"
include "eqid.mm"
include "subgss.mm"
include "sselda.mm"
include "grplid.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "cin.mm"
include "csn.mm"
include "lsmub2.mm"
include "subg0cl.mm"
include "simpr.mm"
include "pj1eq.mm"
include "mpbid.mm"
include "simpld.mm"

theorem pj1rid
  let wph: wff ph
  let cP: class P
  let c.pl: class .+
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let cG: class G
  let cX: class X
  let c.0: class .0.
  let cZ: class Z
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume pj1eu.a: |- .+ = ( +g ` G )
  assume pj1eu.s: |- .(+) = ( LSSum ` G )
  assume pj1eu.o: |- .0. = ( 0g ` G )
  assume pj1eu.z: |- Z = ( Cntz ` G )
  assume pj1eu.2: |- ( ph -> T e. ( SubGrp ` G ) )
  assume pj1eu.3: |- ( ph -> U e. ( SubGrp ` G ) )
  assume pj1eu.4: |- ( ph -> ( T i^i U ) = { .0. } )
  assume pj1eu.5: |- ( ph -> T C_ ( Z ` U ) )
  assume pj1f.p: |- P = ( proj1 ` G )


  assert |- ( ( ph /\ X e. U ) -> ( ( T P U ) ` X ) = .0. )

  proof
    wph
    cX
    cU
    wcel
    #
    wa
    #
    cX
    cT
    cU
    cP
    co
    cfv
    c.0
    wceq
    #
    cX
    cU
    cT
    cP
    co
    cfv
    cX
    wceq
    #
    @1
    cX
    c.0
    cX
    c.pl
    co
    #
    wceq
    @2
    @3
    wa
    @1
    @4
    cX
    @1
    cG
    cgrp
    wcel
    #
    cX
    cG
    cbs
    cfv
    #
    wcel
    @4
    cX
    wceq
    @1
    cT
    cG
    csubg
    cfv
    #
    wcel
    #
    @5
    wph
    @8
    @0
    pj1eu.2
    adantr
    #
    cT
    cG
    subgrcl
    syl
    wph
    cU
    @6
    cX
    wph
    cU
    @7
    wcel
    #
    cU
    @6
    wss
    pj1eu.3
    @6
    cU
    cG
    @6
    eqid
    #
    subgss
    syl
    sselda
    @6
    c.pl
    cG
    cX
    c.0
    @11
    pj1eu.a
    pj1eu.o
    grplid
    syl2anc
    eqcomd
    @1
    c.0
    cX
    cP
    c.pl
    c.po
    cT
    cU
    cG
    cX
    c.0
    cZ
    pj1eu.a
    pj1eu.s
    pj1eu.o
    pj1eu.z
    @9
    wph
    @10
    @0
    pj1eu.3
    adantr
    wph
    cT
    cU
    cin
    c.0
    csn
    wceq
    @0
    pj1eu.4
    adantr
    wph
    cT
    cU
    cZ
    cfv
    wss
    @0
    pj1eu.5
    adantr
    pj1f.p
    wph
    cU
    cT
    cU
    c.po
    co
    #
    cX
    wph
    @8
    @10
    cU
    @12
    wss
    pj1eu.2
    pj1eu.3
    c.po
    cT
    cU
    cG
    pj1eu.s
    lsmub2
    syl2anc
    sselda
    @1
    @8
    c.0
    cT
    wcel
    @9
    cT
    cG
    c.0
    pj1eu.o
    subg0cl
    syl
    wph
    @0
    simpr
    pj1eq
    mpbid
    simpld
end
