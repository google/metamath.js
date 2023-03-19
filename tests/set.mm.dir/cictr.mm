include "ccat.mm"
include "wcel.mm"
include "ccic.mm"
include "cfv.mm"
include "wbr.mm"
include "w3a.mm"
include "cbs.mm"
include "wa.mm"
include "ciclcl.mm"
include "cicrcl.mm"
include "jca.mm"
include "ex.mm"
include "anim12d.mm"
include "3impib.mm"
include "wi.mm"
include "cv.mm"
include "ciso.mm"
include "co.mm"
include "wex.mm"
include "eqid.mm"
include "simpl.mm"
include "simpll.mm"
include "adantl.mm"
include "simplr.mm"
include "cic.mm"
include "simprr.mm"
include "anbi12d.mm"
include "cop.mm"
include "cco.mm"
include "isoco.mm"
include "brcici.mm"
include "exlimiv.mm"
include "com12.mm"
include "imp.mm"
include "sylbid.mm"
include "com23.mm"
include "mpd.mm"

theorem cictr
  let cC: class C
  let cR: class R
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vg: setvar g


  assert |- ( ( C e. Cat /\ R ( ~=c ` C ) S /\ S ( ~=c ` C ) T ) -> R ( ~=c ` C ) T )

  proof
    cC
    ccat
    wcel
    #
    cR
    cS
    cC
    ccic
    cfv
    #
    wbr
    #
    cS
    cT
    @1
    wbr
    #
    w3a
    cR
    cC
    cbs
    cfv
    #
    wcel
    #
    cS
    @4
    wcel
    #
    wa
    #
    cT
    @4
    wcel
    #
    wa
    #
    cR
    cT
    @1
    wbr
    #
    @0
    @2
    @3
    @9
    @0
    @2
    @7
    @3
    @8
    @0
    @2
    @7
    @0
    @2
    wa
    @5
    @6
    cC
    cR
    cS
    ciclcl
    cC
    cR
    cS
    cicrcl
    jca
    ex
    @0
    @3
    @8
    cC
    cS
    cT
    cicrcl
    ex
    anim12d
    3impib
    @0
    @2
    @3
    @9
    @10
    wi
    @0
    @9
    @2
    @3
    wa
    #
    @10
    @0
    @9
    @11
    @10
    wi
    @0
    @9
    wa
    #
    @11
    vf
    cv
    #
    cR
    cS
    cC
    ciso
    cfv
    #
    co
    wcel
    #
    vf
    wex
    #
    vg
    cv
    #
    cS
    cT
    @14
    co
    wcel
    #
    vg
    wex
    #
    wa
    #
    @10
    @12
    @2
    @16
    @3
    @19
    @12
    @4
    cC
    vf
    @14
    cR
    cS
    @14
    eqid
    #
    @4
    eqid
    #
    @0
    @9
    simpl
    #
    @9
    @5
    @0
    @5
    @6
    @8
    simpll
    adantl
    #
    @9
    @6
    @0
    @5
    @6
    @8
    simplr
    adantl
    #
    cic
    @12
    @4
    cC
    vg
    @14
    cS
    cT
    @21
    @22
    @23
    @25
    @0
    @7
    @8
    simprr
    #
    cic
    anbi12d
    @20
    @12
    @10
    @16
    @19
    @12
    @10
    wi
    #
    @15
    @19
    @27
    wi
    vf
    @19
    @15
    @27
    @18
    @15
    @27
    wi
    vg
    @18
    @15
    @27
    @18
    @15
    wa
    #
    @12
    @10
    @28
    @12
    wa
    #
    @4
    cC
    @17
    @13
    cR
    cS
    cop
    cT
    cC
    cco
    cfv
    #
    co
    co
    @14
    cR
    cT
    @21
    @22
    @12
    @0
    @28
    @23
    adantl
    #
    @12
    @5
    @28
    @24
    adantl
    #
    @12
    @8
    @28
    @26
    adantl
    #
    @29
    @4
    cC
    @30
    @13
    @17
    @14
    cR
    cS
    cT
    @22
    @30
    eqid
    @21
    @31
    @32
    @12
    @6
    @28
    @25
    adantl
    @33
    @18
    @15
    @12
    simplr
    @18
    @15
    @12
    simpll
    isoco
    brcici
    ex
    ex
    exlimiv
    com12
    exlimiv
    imp
    com12
    sylbid
    ex
    com23
    3impib
    mpd
end
