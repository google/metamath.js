include "ccla.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "simpl.mm"
include "cpw.mm"
include "cdm.mm"
include "cbs.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elpw2.mm"
include "biimpri.mm"
include "adantl.mm"
include "cpo.mm"
include "wceq.mm"
include "isclat.mm"
include "biimpi.mm"
include "adantr.mm"
include "syl.mm"
include "eleqtrrd.mm"
include "lubcl.mm"
include "simprrd.mm"
include "glbcl.mm"
include "jca.mm"

theorem clatlem
  let cB: class B
  let cS: class S
  let cU: class U
  let cG: class G
  let cK: class K
  assume clatlem.b: |- B = ( Base ` K )
  assume clatlem.u: |- U = ( lub ` K )
  assume clatlem.g: |- G = ( glb ` K )


  assert |- ( ( K e. CLat /\ S C_ B ) -> ( ( U ` S ) e. B /\ ( G ` S ) e. B ) )

  proof
    cK
    ccla
    wcel
    #
    cS
    cB
    wss
    #
    wa
    #
    cS
    cU
    cfv
    cB
    wcel
    cS
    cG
    cfv
    cB
    wcel
    @2
    cB
    cS
    cU
    cK
    ccla
    clatlem.b
    clatlem.u
    @0
    @1
    simpl
    #
    @2
    cS
    cB
    cpw
    #
    cU
    cdm
    #
    @1
    cS
    @4
    wcel
    #
    @0
    @6
    @1
    cS
    cB
    cB
    cK
    cbs
    cfv
    cvv
    clatlem.b
    cK
    cbs
    fvex
    eqeltri
    elpw2
    biimpri
    adantl
    #
    @2
    cK
    cpo
    wcel
    #
    @5
    @4
    wceq
    #
    cG
    cdm
    #
    @4
    wceq
    #
    wa
    #
    wa
    #
    @9
    @0
    @13
    @1
    @0
    @13
    cB
    cU
    cG
    cK
    clatlem.b
    clatlem.u
    clatlem.g
    isclat
    biimpi
    adantr
    #
    @12
    @9
    @8
    @9
    @11
    simpl
    adantl
    syl
    eleqtrrd
    lubcl
    @2
    cB
    cS
    cG
    cK
    ccla
    clatlem.b
    clatlem.g
    @3
    @2
    cS
    @4
    @10
    @7
    @2
    @8
    @9
    @11
    @14
    simprrd
    eleqtrrd
    glbcl
    jca
end
