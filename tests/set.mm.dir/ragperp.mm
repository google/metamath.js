include "cperpg.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "cs3.mm"
include "crag.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "cmir.mm"
include "eqid.mm"
include "cstrkg.mm"
include "adantr.mm"
include "crn.mm"
include "simprr.mm"
include "tglnpt.mm"
include "cin.mm"
include "inss1.mm"
include "sseldi.mm"
include "simprl.mm"
include "wne.mm"
include "wceq.mm"
include "co.mm"
include "wn.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "neqned.mm"
include "tglinethru.mm"
include "eleqtrd.mm"
include "ex.mm"
include "orrd.mm"
include "orcomd.mm"
include "ragcol.mm"
include "ragcom.mm"
include "inss2.mm"
include "ralrimivva.mm"
include "isperp2.mm"
include "mpbird.mm"

theorem ragperp
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cU: class U
  let cG: class G
  let cI: class I
  let cL: class L
  let c.mi: class .-
  let cV: class V
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vg: setvar g
  assume isperp.p: |- P = ( Base ` G )
  assume isperp.d: |- .- = ( dist ` G )
  assume isperp.i: |- I = ( Itv ` G )
  assume isperp.l: |- L = ( LineG ` G )
  assume isperp.g: |- ( ph -> G e. TarskiG )
  assume isperp.a: |- ( ph -> A e. ran L )
  assume ragperp.b: |- ( ph -> B e. ran L )
  assume ragperp.x: |- ( ph -> X e. ( A i^i B ) )
  assume ragperp.u: |- ( ph -> U e. A )
  assume ragperp.v: |- ( ph -> V e. B )
  assume ragperp.1: |- ( ph -> U =/= X )
  assume ragperp.2: |- ( ph -> V =/= X )
  assume ragperp.r: |- ( ph -> <" U X V "> e. ( raG ` G ) )


  assert |- ( ph -> A ( perpG ` G ) B )

  proof
    wph
    cA
    cB
    cG
    cperpg
    cfv
    wbr
    vu
    cv
    #
    cX
    vv
    cv
    #
    cs3
    cG
    crag
    cfv
    #
    wcel
    #
    vv
    cB
    wral
    vu
    cA
    wral
    wph
    @3
    vu
    vv
    cA
    cB
    wph
    @0
    cA
    wcel
    #
    @1
    cB
    wcel
    #
    wa
    #
    wa
    #
    @1
    cX
    @0
    cP
    cG
    cmir
    cfv
    #
    cG
    cI
    cL
    c.mi
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    @8
    eqid
    #
    wph
    cG
    cstrkg
    wcel
    #
    @6
    isperp.g
    adantr
    #
    @7
    cB
    cP
    cG
    cI
    cL
    @1
    isperp.p
    isperp.l
    isperp.i
    @11
    wph
    cB
    cL
    crn
    #
    wcel
    #
    @6
    ragperp.b
    adantr
    #
    wph
    @4
    @5
    simprr
    #
    tglnpt
    #
    @7
    cA
    cP
    cG
    cI
    cL
    cX
    isperp.p
    isperp.l
    isperp.i
    @11
    wph
    cA
    @12
    wcel
    #
    @6
    isperp.a
    adantr
    #
    wph
    cX
    cA
    wcel
    #
    @6
    wph
    cA
    cB
    cin
    #
    cA
    cX
    cA
    cB
    inss1
    ragperp.x
    sseldi
    #
    adantr
    tglnpt
    #
    @7
    cA
    cP
    cG
    cI
    cL
    @0
    isperp.p
    isperp.l
    isperp.i
    @11
    @18
    wph
    @4
    @5
    simprl
    #
    tglnpt
    #
    @7
    cV
    cX
    @0
    @1
    cP
    @8
    cG
    cI
    cL
    c.mi
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    @9
    @11
    @7
    cB
    cP
    cG
    cI
    cL
    cV
    isperp.p
    isperp.l
    isperp.i
    @11
    @14
    wph
    cV
    cB
    wcel
    #
    @6
    ragperp.v
    adantr
    tglnpt
    #
    @22
    @24
    @16
    @7
    @0
    cX
    cV
    cP
    @8
    cG
    cI
    cL
    c.mi
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    @9
    @11
    @24
    @22
    @26
    @7
    cU
    cX
    cV
    @0
    cP
    @8
    cG
    cI
    cL
    c.mi
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    @9
    @11
    @7
    cA
    cP
    cG
    cI
    cL
    cU
    isperp.p
    isperp.l
    isperp.i
    @11
    @18
    wph
    cU
    cA
    wcel
    #
    @6
    ragperp.u
    adantr
    tglnpt
    @22
    @26
    @24
    wph
    cU
    cX
    cV
    cs3
    @2
    wcel
    @6
    ragperp.r
    adantr
    wph
    cU
    cX
    wne
    @6
    ragperp.1
    adantr
    @7
    cX
    @0
    wceq
    #
    cU
    cX
    @0
    cL
    co
    #
    wcel
    #
    @7
    @28
    @30
    @7
    @28
    wn
    #
    @30
    @7
    @31
    wa
    #
    cU
    cA
    @29
    wph
    @27
    @6
    @31
    ragperp.u
    ad2antrr
    @32
    cA
    cP
    cX
    @0
    cG
    cI
    cL
    isperp.p
    isperp.i
    isperp.l
    wph
    @10
    @6
    @31
    isperp.g
    ad2antrr
    @7
    cX
    cP
    wcel
    #
    @31
    @22
    adantr
    @7
    @0
    cP
    wcel
    @31
    @24
    adantr
    @32
    cX
    @0
    @7
    @31
    simpr
    neqned
    #
    @34
    wph
    @17
    @6
    @31
    isperp.a
    ad2antrr
    wph
    @19
    @6
    @31
    @21
    ad2antrr
    @7
    @4
    @31
    @23
    adantr
    tglinethru
    eleqtrd
    ex
    orrd
    orcomd
    ragcol
    ragcom
    wph
    cV
    cX
    wne
    @6
    ragperp.2
    adantr
    @7
    cX
    @1
    wceq
    #
    cV
    cX
    @1
    cL
    co
    #
    wcel
    #
    @7
    @35
    @37
    @7
    @35
    wn
    #
    @37
    @7
    @38
    wa
    #
    cV
    cB
    @36
    wph
    @25
    @6
    @38
    ragperp.v
    ad2antrr
    @39
    cB
    cP
    cX
    @1
    cG
    cI
    cL
    isperp.p
    isperp.i
    isperp.l
    wph
    @10
    @6
    @38
    isperp.g
    ad2antrr
    @7
    @33
    @38
    @22
    adantr
    @7
    @1
    cP
    wcel
    @38
    @16
    adantr
    @39
    cX
    @1
    @7
    @38
    simpr
    neqned
    #
    @40
    wph
    @13
    @6
    @38
    ragperp.b
    ad2antrr
    wph
    cX
    cB
    wcel
    @6
    @38
    wph
    @20
    cB
    cX
    cA
    cB
    inss2
    ragperp.x
    sseldi
    ad2antrr
    @7
    @5
    @38
    @15
    adantr
    tglinethru
    eleqtrd
    ex
    orrd
    orcomd
    ragcol
    ragcom
    ralrimivva
    wph
    vv
    vu
    cA
    cB
    cP
    cG
    cI
    cL
    c.mi
    cX
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    isperp.g
    isperp.a
    ragperp.b
    ragperp.x
    isperp2
    mpbird
end
