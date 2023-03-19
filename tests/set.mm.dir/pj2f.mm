include "co.mm"
include "wf.mm"
include "cin.mm"
include "csn.mm"
include "incom.mm"
include "syl5eq.mm"
include "cntzrecd.mm"
include "pj1f.mm"
include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wceq.mm"
include "lsmcom2.mm"
include "syl3anc.mm"
include "feq2d.mm"
include "mpbird.mm"

theorem pj2f
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


  assert |- ( ph -> ( U P T ) : ( T .(+) U ) --> U )

  proof
    wph
    cT
    cU
    c.po
    co
    #
    cU
    cU
    cT
    cP
    co
    #
    wf
    cU
    cT
    c.po
    co
    #
    cU
    @1
    wf
    wph
    cP
    c.pl
    c.po
    cU
    cT
    cG
    c.0
    cZ
    pj1eu.a
    pj1eu.s
    pj1eu.o
    pj1eu.z
    pj1eu.3
    pj1eu.2
    wph
    cU
    cT
    cin
    cT
    cU
    cin
    c.0
    csn
    cU
    cT
    incom
    pj1eu.4
    syl5eq
    wph
    cT
    cU
    cG
    cZ
    pj1eu.z
    pj1eu.2
    pj1eu.3
    pj1eu.5
    cntzrecd
    pj1f.p
    pj1f
    wph
    @0
    @2
    cU
    @1
    wph
    cT
    cG
    csubg
    cfv
    #
    wcel
    cU
    @3
    wcel
    cT
    cU
    cZ
    cfv
    wss
    @0
    @2
    wceq
    pj1eu.2
    pj1eu.3
    pj1eu.5
    c.po
    cT
    cU
    cG
    cZ
    pj1eu.s
    pj1eu.z
    lsmcom2
    syl3anc
    feq2d
    mpbird
end
