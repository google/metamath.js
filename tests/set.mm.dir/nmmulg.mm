include "cnlm.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "co.mm"
include "cnm.mm"
include "cfv.mm"
include "csca.mm"
include "cmul.mm"
include "cabs.mm"
include "cbs.mm"
include "wceq.mm"
include "simp2.mm"
include "zring.mm"
include "zringbas.mm"
include "cabl.mm"
include "clmod.mm"
include "nlmlmod.mm"
include "zlmlmod.mm"
include "sylibr.mm"
include "3ad2ant1.mm"
include "zlmsca.mm"
include "syl.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "eleqtrd.mm"
include "zlmbas.mm"
include "eqid.mm"
include "zlmvsca.mm"
include "nmvs.mm"
include "syld3an2.mm"
include "zlmnm.mm"
include "fveq1d.mm"
include "zzsnm.mm"
include "3ad2ant2.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"

theorem nmmulg
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cM: class M
  let cN: class N
  let cX: class X
  let cZ: class Z
  assume nmmulg.x: |- B = ( Base ` R )
  assume nmmulg.n: |- N = ( norm ` R )
  assume nmmulg.z: |- Z = ( ZMod ` R )
  assume nmmulg.t: |- .x. = ( .g ` R )


  assert |- ( ( Z e. NrmMod /\ M e. ZZ /\ X e. B ) -> ( N ` ( M .x. X ) ) = ( ( abs ` M ) x. ( N ` X ) ) )

  proof
    cZ
    cnlm
    wcel
    #
    cM
    cz
    wcel
    #
    cX
    cB
    wcel
    #
    w3a
    #
    cM
    cX
    c.x
    co
    #
    cZ
    cnm
    cfv
    #
    cfv
    #
    cM
    cZ
    csca
    cfv
    #
    cnm
    cfv
    #
    cfv
    #
    cX
    @5
    cfv
    #
    cmul
    co
    #
    @4
    cN
    cfv
    cM
    cabs
    cfv
    #
    cX
    cN
    cfv
    #
    cmul
    co
    @0
    cM
    @7
    cbs
    cfv
    #
    wcel
    @1
    @2
    @6
    @11
    wceq
    @3
    cM
    cz
    @14
    @0
    @1
    @2
    simp2
    @3
    cz
    zring
    cbs
    cfv
    @14
    zringbas
    @3
    zring
    @7
    cbs
    @3
    cR
    cabl
    wcel
    #
    zring
    @7
    wceq
    @0
    @1
    @15
    @2
    @0
    cZ
    clmod
    wcel
    @15
    cZ
    nlmlmod
    cR
    cZ
    nmmulg.z
    zlmlmod
    sylibr
    3ad2ant1
    #
    cR
    cabl
    cZ
    nmmulg.z
    zlmsca
    syl
    #
    fveq2d
    syl5eq
    eleqtrd
    @8
    c.x
    @7
    @14
    @5
    cB
    cZ
    cM
    cX
    cB
    cR
    cZ
    nmmulg.z
    nmmulg.x
    zlmbas
    @5
    eqid
    c.x
    cR
    cZ
    nmmulg.z
    nmmulg.t
    zlmvsca
    @7
    eqid
    @14
    eqid
    @8
    eqid
    nmvs
    syld3an2
    @3
    @4
    cN
    @5
    @3
    @15
    cN
    @5
    wceq
    @16
    cR
    cN
    cabl
    cZ
    nmmulg.z
    nmmulg.n
    zlmnm
    syl
    #
    fveq1d
    @3
    @12
    @9
    @13
    @10
    cmul
    @3
    @12
    cM
    zring
    cnm
    cfv
    #
    cfv
    #
    @9
    @1
    @0
    @12
    @20
    wceq
    @2
    cM
    zzsnm
    3ad2ant2
    @3
    cM
    @19
    @8
    @3
    zring
    @7
    cnm
    @17
    fveq2d
    fveq1d
    eqtrd
    @3
    cX
    cN
    @5
    @18
    fveq1d
    oveq12d
    3eqtr4d
end
