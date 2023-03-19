include "co.mm"
include "wceq.mm"
include "cfv.mm"
include "wa.mm"
include "wcel.mm"
include "pj1id.mm"
include "mpdan.mm"
include "eqeq1d.mm"
include "pj1f.mm"
include "ffvelrnd.mm"
include "pj2f.mm"
include "subgdisjb.mm"
include "bitrd.mm"

theorem pj1eq
  let wph: wff ph
  let cB: class B
  let cC: class C
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
  assume pj1eq.5: |- ( ph -> X e. ( T .(+) U ) )
  assume pj1eq.6: |- ( ph -> B e. T )
  assume pj1eq.7: |- ( ph -> C e. U )


  assert |- ( ph -> ( X = ( B .+ C ) <-> ( ( ( T P U ) ` X ) = B /\ ( ( U P T ) ` X ) = C ) ) )

  proof
    wph
    cX
    cB
    cC
    c.pl
    co
    #
    wceq
    cX
    cT
    cU
    cP
    co
    #
    cfv
    #
    cX
    cU
    cT
    cP
    co
    #
    cfv
    #
    c.pl
    co
    #
    @0
    wceq
    @2
    cB
    wceq
    @4
    cC
    wceq
    wa
    wph
    cX
    @5
    @0
    wph
    cX
    cT
    cU
    c.po
    co
    #
    wcel
    cX
    @5
    wceq
    pj1eq.5
    wph
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
    pj1eu.2
    pj1eu.3
    pj1eu.4
    pj1eu.5
    pj1f.p
    pj1id
    mpdan
    eqeq1d
    wph
    @2
    @4
    cB
    cC
    c.pl
    cT
    cU
    cG
    c.0
    cZ
    pj1eu.a
    pj1eu.o
    pj1eu.z
    pj1eu.2
    pj1eu.3
    pj1eu.4
    pj1eu.5
    wph
    @6
    cT
    cX
    @1
    wph
    cP
    c.pl
    c.po
    cT
    cU
    cG
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
    pj1f.p
    pj1f
    pj1eq.5
    ffvelrnd
    pj1eq.6
    wph
    @6
    cU
    cX
    @3
    wph
    cP
    c.pl
    c.po
    cT
    cU
    cG
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
    pj1f.p
    pj2f
    pj1eq.5
    ffvelrnd
    pj1eq.7
    subgdisjb
    bitrd
end
