include "co.mm"
include "cress.mm"
include "cghm.mm"
include "wcel.mm"
include "pj1ghm.mm"
include "csubg.mm"
include "cfv.mm"
include "crn.mm"
include "wss.mm"
include "wb.mm"
include "wf.mm"
include "pj1f.mm"
include "frn.mm"
include "syl.mm"
include "eqid.mm"
include "resghm2b.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem pj1ghm2
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


  assert |- ( ph -> ( T P U ) e. ( ( G |`s ( T .(+) U ) ) GrpHom ( G |`s T ) ) )

  proof
    wph
    cT
    cU
    cP
    co
    #
    cG
    cT
    cU
    c.po
    co
    #
    cress
    co
    #
    cG
    cghm
    co
    wcel
    #
    @0
    @2
    cG
    cT
    cress
    co
    #
    cghm
    co
    wcel
    #
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
    pj1ghm
    wph
    cT
    cG
    csubg
    cfv
    wcel
    @0
    crn
    cT
    wss
    #
    @3
    @5
    wb
    pj1eu.2
    wph
    @1
    cT
    @0
    wf
    @6
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
    @1
    cT
    @0
    frn
    syl
    @2
    cG
    @4
    @0
    cT
    @4
    eqid
    resghm2b
    syl2anc
    mpbid
end
