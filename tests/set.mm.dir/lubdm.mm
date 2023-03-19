include "cdm.mm"
include "cpw.mm"
include "crio.mm"
include "cmpt.mm"
include "wreu.mm"
include "cab.mm"
include "cres.mm"
include "crab.mm"
include "lubfval.mm"
include "dmeqd.mm"
include "cin.mm"
include "riotaex.mm"
include "eqid.mm"
include "dmmpti.mm"
include "ineq2i.mm"
include "dmres.mm"
include "dfrab2.mm"
include "3eqtr4i.mm"
include "syl6eq.mm"

theorem lubdm
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cU: class U
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let vs: setvar s
  let vp: setvar p
  assume lubfval.b: |- B = ( Base ` K )
  assume lubfval.l: |- .<_ = ( le ` K )
  assume lubfval.u: |- U = ( lub ` K )
  assume lubfval.p: |- ( ps <-> ( A. y e. s y .<_ x /\ A. z e. B ( A. y e. s y .<_ z -> x .<_ z ) ) )
  assume lubfval.k: |- ( ph -> K e. V )

  disjoint s x
  disjoint s z
  disjoint B s
  disjoint x z
  disjoint B x
  disjoint B z
  disjoint s y
  disjoint K s
  disjoint x y
  disjoint K x
  disjoint y z
  disjoint K y
  disjoint K z
  disjoint p s
  disjoint p x
  disjoint p z
  disjoint B p
  disjoint p y
  disjoint K p
  disjoint .<_ p
  assert |- ( ph -> dom U = { s e. ~P B | E! x e. B ps } )

  proof
    wph
    cU
    cdm
    vs
    cB
    cpw
    #
    wps
    vx
    cB
    crio
    #
    cmpt
    #
    wps
    vx
    cB
    wreu
    #
    vs
    cab
    #
    cres
    #
    cdm
    #
    @3
    vs
    @0
    crab
    #
    wph
    cU
    @5
    wph
    wps
    vx
    vy
    vz
    cB
    cU
    cK
    c.le
    cV
    vs
    lubfval.b
    lubfval.l
    lubfval.u
    lubfval.p
    lubfval.k
    lubfval
    dmeqd
    @4
    @2
    cdm
    #
    cin
    @4
    @0
    cin
    @6
    @7
    @8
    @0
    @4
    vs
    @0
    @1
    @2
    wps
    vx
    cB
    riotaex
    @2
    eqid
    dmmpti
    ineq2i
    @2
    @4
    dmres
    @3
    vs
    @0
    dfrab2
    3eqtr4i
    syl6eq
end
