include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cint.mm"
include "cple.mm"
include "eqid.mm"
include "cbs.mm"
include "wceq.mm"
include "ipobas.mm"
include "3ad2ant1.mm"
include "cglb.mm"
include "a1i.mm"
include "cpo.mm"
include "ipopos.mm"
include "simp2.mm"
include "mreintcl.mm"
include "cv.mm"
include "wa.mm"
include "wbr.mm"
include "intss1.mm"
include "adantl.mm"
include "wb.mm"
include "simpl1.mm"
include "adantr.mm"
include "sselda.mm"
include "ipole.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "wral.mm"
include "simpll1.mm"
include "simplr.mm"
include "simpl2.mm"
include "biimpd.mm"
include "ralimdva.mm"
include "3impia.mm"
include "ssint.mm"
include "sylibr.mm"
include "simp11.mm"
include "posglbd.mm"

theorem mrelatglb
  let cC: class C
  let cU: class U
  let cG: class G
  let cI: class I
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cL: class L
  let cF: class F
  assume mreclat.i: |- I = ( toInc ` C )
  assume mrelatglb.g: |- G = ( glb ` I )


  assert |- ( ( C e. ( Moore ` X ) /\ U C_ C /\ U =/= (/) ) -> ( G ` U ) = |^| U )

  proof
    cC
    cX
    cmre
    cfv
    #
    wcel
    #
    cU
    cC
    wss
    #
    cU
    c0
    wne
    #
    w3a
    #
    vx
    vy
    cC
    cU
    cU
    cint
    #
    cG
    cI
    cI
    cple
    cfv
    #
    @6
    eqid
    #
    @1
    @2
    cC
    cI
    cbs
    cfv
    wceq
    @3
    cC
    cI
    @0
    mreclat.i
    ipobas
    3ad2ant1
    cG
    cI
    cglb
    cfv
    wceq
    @4
    mrelatglb.g
    a1i
    cI
    cpo
    wcel
    @4
    cC
    cI
    mreclat.i
    ipopos
    a1i
    @1
    @2
    @3
    simp2
    #
    cC
    cU
    cX
    mreintcl
    #
    @4
    vx
    cv
    #
    cU
    wcel
    #
    wa
    #
    @5
    @10
    @6
    wbr
    #
    @5
    @10
    wss
    #
    @11
    @14
    @4
    @10
    cU
    intss1
    adantl
    @12
    @1
    @5
    cC
    wcel
    #
    @10
    cC
    wcel
    #
    @13
    @14
    wb
    @1
    @2
    @3
    @11
    simpl1
    @4
    @15
    @11
    @9
    adantr
    @4
    cU
    cC
    @10
    @8
    sselda
    cC
    cI
    @6
    @0
    @5
    @10
    mreclat.i
    @7
    ipole
    syl3anc
    mpbird
    @4
    vy
    cv
    #
    cC
    wcel
    #
    @17
    @10
    @6
    wbr
    #
    vx
    cU
    wral
    #
    w3a
    #
    @17
    @5
    @6
    wbr
    #
    @17
    @5
    wss
    #
    @21
    @17
    @10
    wss
    #
    vx
    cU
    wral
    #
    @23
    @4
    @18
    @20
    @25
    @4
    @18
    wa
    #
    @19
    @24
    vx
    cU
    @26
    @11
    wa
    #
    @19
    @24
    @27
    @1
    @18
    @16
    @19
    @24
    wb
    @1
    @2
    @3
    @18
    @11
    simpll1
    @4
    @18
    @11
    simplr
    @26
    cU
    cC
    @10
    @1
    @2
    @3
    @18
    simpl2
    sselda
    cC
    cI
    @6
    @0
    @17
    @10
    mreclat.i
    @7
    ipole
    syl3anc
    biimpd
    ralimdva
    3impia
    vx
    @17
    cU
    ssint
    sylibr
    @21
    @1
    @18
    @15
    @22
    @23
    wb
    @1
    @2
    @3
    @18
    @20
    simp11
    @4
    @18
    @20
    simp2
    @4
    @18
    @15
    @20
    @9
    3ad2ant1
    cC
    cI
    @6
    @0
    @17
    @5
    mreclat.i
    @7
    ipole
    syl3anc
    mpbird
    posglbd
end
