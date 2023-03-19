include "ccla.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "csn.mm"
include "cfv.mm"
include "wceq.mm"
include "clat.mm"
include "wa.mm"
include "clatl.mm"
include "ssel.mm"
include "impcom.mm"
include "lubsn.mm"
include "syl2an.mm"
include "3impb.mm"
include "wbr.mm"
include "snssi.mm"
include "lubss.mm"
include "syl3an3.mm"
include "3com23.mm"
include "eqbrtrrd.mm"

theorem lubel
  let cB: class B
  let cS: class S
  let cU: class U
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let vz: setvar z
  let vy: setvar y
  let cT: class T
  assume lublem.b: |- B = ( Base ` K )
  assume lublem.l: |- .<_ = ( le ` K )
  assume lublem.u: |- U = ( lub ` K )


  assert |- ( ( K e. CLat /\ X e. S /\ S C_ B ) -> X .<_ ( U ` S ) )

  proof
    cK
    ccla
    wcel
    #
    cX
    cS
    wcel
    #
    cS
    cB
    wss
    #
    w3a
    cX
    csn
    #
    cU
    cfv
    #
    cX
    cS
    cU
    cfv
    #
    c.le
    @0
    @1
    @2
    @4
    cX
    wceq
    #
    @0
    cK
    clat
    wcel
    cX
    cB
    wcel
    #
    @6
    @1
    @2
    wa
    cK
    clatl
    @2
    @1
    @7
    cS
    cB
    cX
    ssel
    impcom
    cB
    cU
    cK
    cX
    lublem.b
    lublem.u
    lubsn
    syl2an
    3impb
    @0
    @2
    @1
    @4
    @5
    c.le
    wbr
    #
    @1
    @0
    @2
    @3
    cS
    wss
    @8
    cX
    cS
    snssi
    cB
    @3
    cS
    cU
    cK
    c.le
    lublem.b
    lublem.l
    lublem.u
    lubss
    syl3an3
    3com23
    eqbrtrrd
end
