include "cv.mm"
include "cs3.mm"
include "crag.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wne.mm"
include "cin.mm"
include "wa.mm"
include "co.mm"
include "cstrkg.mm"
include "adantr.mm"
include "ad5antr.mm"
include "crn.mm"
include "inss1.mm"
include "simpr.mm"
include "sseldi.mm"
include "ad4antr.mm"
include "tglnpt.mm"
include "adantl4r.mm"
include "simplr.mm"
include "simp-4r.mm"
include "cmir.mm"
include "eqid.mm"
include "simp-5r.mm"
include "wceq.mm"
include "id.mm"
include "eqidd.mm"
include "s3eqd.mm"
include "eleq1d.mm"
include "rspc2va.mm"
include "syl21anc.mm"
include "simpllr.mm"
include "necomd.mm"
include "ragncol.mm"
include "ncolrot2.mm"
include "tglineneq.mm"
include "tglinethru.mm"
include "inss2.mm"
include "3netr4d.mm"
include "wrex.mm"
include "tglnpt2.mm"
include "ad3antrrr.mm"
include "r19.29a.mm"
include "cperpg.mm"
include "wbr.mm"
include "isperp.mm"
include "mpbid.mm"

theorem perpneq
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let c.mi: class .-
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let va: setvar a
  let vb: setvar b
  let vg: setvar g
  assume isperp.p: |- P = ( Base ` G )
  assume isperp.d: |- .- = ( dist ` G )
  assume isperp.i: |- I = ( Itv ` G )
  assume isperp.l: |- L = ( LineG ` G )
  assume isperp.g: |- ( ph -> G e. TarskiG )
  assume isperp.a: |- ( ph -> A e. ran L )
  assume isperp.b: |- ( ph -> B e. ran L )
  assume perpcom.1: |- ( ph -> A ( perpG ` G ) B )


  assert |- ( ph -> A =/= B )

  proof
    wph
    vy
    cv
    #
    vx
    cv
    #
    vz
    cv
    #
    cs3
    #
    cG
    crag
    cfv
    #
    wcel
    #
    vz
    cB
    wral
    vy
    cA
    wral
    #
    cA
    cB
    wne
    #
    vx
    cA
    cB
    cin
    #
    wph
    @1
    @8
    wcel
    #
    wa
    #
    @6
    wa
    #
    @1
    vu
    cv
    #
    wne
    #
    @7
    vu
    cA
    @11
    @12
    cA
    wcel
    #
    wa
    @13
    wa
    #
    @1
    vv
    cv
    #
    wne
    #
    @7
    vv
    cB
    @15
    @16
    cB
    wcel
    #
    wa
    @17
    wa
    #
    @12
    @1
    cL
    co
    #
    @1
    @16
    cL
    co
    #
    cA
    cB
    @19
    @21
    @20
    @19
    @1
    @16
    @12
    @1
    cP
    cG
    cI
    cL
    isperp.p
    isperp.i
    isperp.l
    @10
    cG
    cstrkg
    wcel
    #
    @6
    @14
    @13
    @18
    @17
    wph
    @22
    @9
    isperp.g
    adantr
    #
    ad5antr
    #
    @10
    @6
    @14
    @13
    @18
    @17
    @1
    cP
    wcel
    @10
    @14
    wa
    #
    @13
    wa
    #
    @18
    wa
    #
    @17
    wa
    #
    cA
    cP
    cG
    cI
    cL
    @1
    isperp.p
    isperp.l
    isperp.i
    wph
    @22
    @9
    @14
    @13
    @18
    @17
    isperp.g
    ad5antr
    #
    wph
    cA
    cL
    crn
    #
    wcel
    #
    @9
    @14
    @13
    @18
    @17
    isperp.a
    ad5antr
    #
    @10
    @1
    cA
    wcel
    @14
    @13
    @18
    @17
    @10
    @8
    cA
    @1
    cA
    cB
    inss1
    wph
    @9
    simpr
    #
    sseldi
    #
    ad4antr
    #
    tglnpt
    #
    adantl4r
    #
    @10
    @6
    @14
    @13
    @18
    @17
    @16
    cP
    wcel
    @28
    cB
    cP
    cG
    cI
    cL
    @16
    isperp.p
    isperp.l
    isperp.i
    @29
    wph
    cB
    @30
    wcel
    #
    @9
    @14
    @13
    @18
    @17
    isperp.b
    ad5antr
    #
    @26
    @18
    @17
    simplr
    #
    tglnpt
    #
    adantl4r
    #
    @10
    @6
    @14
    @13
    @18
    @17
    @12
    cP
    wcel
    @28
    cA
    cP
    cG
    cI
    cL
    @12
    isperp.p
    isperp.l
    isperp.i
    @29
    @32
    @10
    @14
    @13
    @18
    @17
    simp-4r
    #
    tglnpt
    #
    adantl4r
    #
    @37
    @19
    cP
    cG
    cI
    cL
    @12
    @1
    @16
    isperp.p
    isperp.l
    isperp.i
    @24
    @45
    @37
    @42
    @19
    @12
    @1
    @16
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
    @46
    eqid
    @24
    @45
    @37
    @42
    @19
    @14
    @18
    @6
    @12
    @1
    @16
    cs3
    #
    @4
    wcel
    #
    @11
    @14
    @13
    @18
    @17
    simp-4r
    @15
    @18
    @17
    simplr
    @10
    @6
    @14
    @13
    @18
    @17
    simp-5r
    @5
    @48
    @12
    @1
    @2
    cs3
    #
    @4
    wcel
    vy
    vz
    @12
    @16
    cA
    cB
    @0
    @12
    wceq
    #
    @3
    @49
    @4
    @50
    @0
    @1
    @2
    @2
    @12
    @1
    @50
    id
    @50
    @1
    eqidd
    @50
    @2
    eqidd
    s3eqd
    eleq1d
    @2
    @16
    wceq
    #
    @49
    @47
    @4
    @51
    @12
    @1
    @2
    @16
    @12
    @1
    @51
    @12
    eqidd
    @51
    @1
    eqidd
    @51
    id
    s3eqd
    eleq1d
    rspc2va
    syl21anc
    @10
    @6
    @14
    @13
    @18
    @17
    @12
    @1
    wne
    @28
    @1
    @12
    @25
    @13
    @18
    @17
    simpllr
    necomd
    #
    adantl4r
    @10
    @6
    @14
    @13
    @18
    @17
    @16
    @1
    wne
    @28
    @1
    @16
    @27
    @17
    simpr
    #
    necomd
    adantl4r
    ragncol
    ncolrot2
    tglineneq
    necomd
    @10
    @6
    @14
    @13
    @18
    @17
    cA
    @20
    wceq
    @28
    cA
    cP
    @12
    @1
    cG
    cI
    cL
    isperp.p
    isperp.i
    isperp.l
    @29
    @44
    @36
    @52
    @52
    @32
    @43
    @35
    tglinethru
    adantl4r
    @10
    @6
    @14
    @13
    @18
    @17
    cB
    @21
    wceq
    @28
    cB
    cP
    @1
    @16
    cG
    cI
    cL
    isperp.p
    isperp.i
    isperp.l
    @29
    @36
    @41
    @53
    @53
    @39
    @10
    @1
    cB
    wcel
    @14
    @13
    @18
    @17
    @10
    @8
    cB
    @1
    cA
    cB
    inss2
    @33
    sseldi
    #
    ad4antr
    @40
    tglinethru
    adantl4r
    3netr4d
    @10
    @17
    vv
    cB
    wrex
    @6
    @14
    @13
    @10
    vv
    cB
    cP
    cG
    cI
    cL
    @1
    isperp.p
    isperp.i
    isperp.l
    @23
    wph
    @38
    @9
    isperp.b
    adantr
    @54
    tglnpt2
    ad3antrrr
    r19.29a
    @10
    @13
    vu
    cA
    wrex
    @6
    @10
    vu
    cA
    cP
    cG
    cI
    cL
    @1
    isperp.p
    isperp.i
    isperp.l
    @23
    wph
    @31
    @9
    isperp.a
    adantr
    @34
    tglnpt2
    adantr
    r19.29a
    wph
    cA
    cB
    cG
    cperpg
    cfv
    wbr
    @6
    vx
    @8
    wrex
    perpcom.1
    wph
    vx
    vz
    vy
    cA
    cB
    cP
    cG
    cI
    cL
    c.mi
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    isperp.g
    isperp.a
    isperp.b
    isperp
    mpbid
    r19.29a
end
