include "cdm.mm"
include "cpw.mm"
include "crio.mm"
include "cmpt.mm"
include "wreu.mm"
include "cab.mm"
include "cres.mm"
include "crab.mm"
include "glbfval.mm"
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

theorem glbdm
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cG: class G
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let vs: setvar s
  let vp: setvar p
  assume glbfval.b: |- B = ( Base ` K )
  assume glbfval.l: |- .<_ = ( le ` K )
  assume glbfval.g: |- G = ( glb ` K )
  assume glbfval.p: |- ( ps <-> ( A. y e. s x .<_ y /\ A. z e. B ( A. y e. s z .<_ y -> z .<_ x ) ) )
  assume glbfval.k: |- ( ph -> K e. V )

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
  assert |- ( ph -> dom G = { s e. ~P B | E! x e. B ps } )

  proof
    wph
    cG
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
    cG
    @5
    wph
    wps
    vx
    vy
    vz
    cB
    cG
    cK
    c.le
    cV
    vs
    glbfval.b
    glbfval.l
    glbfval.g
    glbfval.p
    glbfval.k
    glbfval
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
