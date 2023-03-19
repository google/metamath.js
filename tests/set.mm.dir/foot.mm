include "cv.mm"
include "co.mm"
include "cperpg.mm"
include "cfv.mm"
include "wbr.mm"
include "wrex.mm"
include "wrmo.mm"
include "wreu.mm"
include "footex.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wcel.mm"
include "cmir.mm"
include "eqid.mm"
include "cstrkg.mm"
include "ad2antrr.mm"
include "adantr.mm"
include "crn.mm"
include "simprl.mm"
include "tglnpt.mm"
include "simprr.mm"
include "cs3.mm"
include "crag.mm"
include "wne.mm"
include "wn.mm"
include "nelne2.mm"
include "syl2anc.mm"
include "necomd.mm"
include "tglinerflx1.mm"
include "wb.mm"
include "tgelrnln.mm"
include "tglinerflx2.mm"
include "elind.mm"
include "isperp2.mm"
include "mpbid.mm"
include "id.mm"
include "eqidd.mm"
include "s3eqd.mm"
include "eleq1d.mm"
include "rspc2va.mm"
include "syl21anc.mm"
include "ragflat.mm"
include "ex.mm"
include "ralrimivva.mm"
include "oveq2.mm"
include "breq1d.mm"
include "rmo4.mm"
include "sylibr.mm"
include "reu5.mm"
include "sylanbrc.mm"

theorem foot
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cC: class C
  let cP: class P
  let cG: class G
  let cI: class I
  let cL: class L
  let c.mi: class .-
  let va: setvar a
  let vb: setvar b
  let vd: setvar d
  let vp: setvar p
  let vq: setvar q
  let vu: setvar u
  let vv: setvar v
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let vg: setvar g
  assume isperp.p: |- P = ( Base ` G )
  assume isperp.d: |- .- = ( dist ` G )
  assume isperp.i: |- I = ( Itv ` G )
  assume isperp.l: |- L = ( LineG ` G )
  assume isperp.g: |- ( ph -> G e. TarskiG )
  assume isperp.a: |- ( ph -> A e. ran L )
  assume foot.x: |- ( ph -> C e. P )
  assume foot.y: |- ( ph -> -. C e. A )

  disjoint A x
  disjoint C x
  disjoint G x
  disjoint I x
  disjoint .- x
  disjoint L x
  disjoint P x
  disjoint ph x
  disjoint A x
  disjoint G x
  disjoint ph x
  disjoint A a
  disjoint A b
  disjoint A d
  disjoint A p
  disjoint A q
  disjoint A u
  disjoint A v
  disjoint A y
  disjoint A z
  disjoint a b
  disjoint a d
  disjoint a p
  disjoint a q
  disjoint a u
  disjoint a v
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b d
  disjoint b p
  disjoint b q
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint d p
  disjoint d q
  disjoint d u
  disjoint d v
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint p q
  disjoint p u
  disjoint p v
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint q u
  disjoint q v
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint C a
  disjoint C b
  disjoint C d
  disjoint C p
  disjoint C q
  disjoint C u
  disjoint C v
  disjoint C y
  disjoint C z
  disjoint G a
  disjoint G b
  disjoint G d
  disjoint G p
  disjoint G q
  disjoint G y
  disjoint G z
  disjoint I a
  disjoint I b
  disjoint I d
  disjoint I p
  disjoint I q
  disjoint I y
  disjoint I z
  disjoint .- d
  disjoint .- p
  disjoint .- q
  disjoint .- y
  disjoint .- z
  disjoint L a
  disjoint L b
  disjoint L d
  disjoint L p
  disjoint L q
  disjoint L u
  disjoint L v
  disjoint L y
  disjoint L z
  disjoint P a
  disjoint P b
  disjoint P d
  disjoint P p
  disjoint P q
  disjoint P y
  disjoint P z
  disjoint a ph
  disjoint b ph
  disjoint d ph
  disjoint p ph
  disjoint ph q
  disjoint ph y
  disjoint ph z
  disjoint a b
  disjoint a u
  disjoint a v
  disjoint a x
  disjoint A a
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint A b
  disjoint u v
  disjoint u x
  disjoint A u
  disjoint v x
  disjoint A v
  disjoint B a
  disjoint B b
  disjoint B u
  disjoint B v
  disjoint B x
  disjoint a g
  disjoint G a
  disjoint b g
  disjoint G b
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint G g
  disjoint G u
  disjoint G v
  disjoint L a
  disjoint L b
  disjoint L g
  disjoint a ph
  disjoint b ph
  disjoint g ph
  disjoint ph u
  disjoint ph v
  assert |- ( ph -> E! x e. A ( C L x ) ( perpG ` G ) A )

  proof
    wph
    cC
    vx
    cv
    #
    cL
    co
    #
    cA
    cG
    cperpg
    cfv
    #
    wbr
    #
    vx
    cA
    wrex
    @3
    vx
    cA
    wrmo
    #
    @3
    vx
    cA
    wreu
    wph
    vx
    cA
    cC
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
    foot.x
    foot.y
    footex
    wph
    @3
    cC
    vz
    cv
    #
    cL
    co
    #
    cA
    @2
    wbr
    #
    wa
    #
    @0
    @5
    wceq
    #
    wi
    #
    vz
    cA
    wral
    vx
    cA
    wral
    @4
    wph
    @10
    vx
    vz
    cA
    cA
    wph
    @0
    cA
    wcel
    #
    @5
    cA
    wcel
    #
    wa
    #
    wa
    #
    @8
    @9
    @14
    @8
    wa
    #
    cC
    @0
    @5
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
    @16
    eqid
    wph
    cG
    cstrkg
    wcel
    #
    @13
    @8
    isperp.g
    ad2antrr
    #
    wph
    cC
    cP
    wcel
    #
    @13
    @8
    foot.x
    ad2antrr
    #
    @14
    @0
    cP
    wcel
    @8
    @14
    cA
    cP
    cG
    cI
    cL
    @0
    isperp.p
    isperp.l
    isperp.i
    wph
    @17
    @13
    isperp.g
    adantr
    #
    wph
    cA
    cL
    crn
    wcel
    @13
    isperp.a
    adantr
    #
    wph
    @11
    @12
    simprl
    #
    tglnpt
    #
    adantr
    #
    @14
    @5
    cP
    wcel
    @8
    @14
    cA
    cP
    cG
    cI
    cL
    @5
    isperp.p
    isperp.l
    isperp.i
    @21
    @22
    wph
    @11
    @12
    simprr
    #
    tglnpt
    #
    adantr
    #
    @15
    cC
    @1
    wcel
    @12
    vu
    cv
    #
    @0
    vv
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
    vv
    cA
    wral
    vu
    @1
    wral
    #
    cC
    @0
    @5
    cs3
    #
    @32
    wcel
    #
    @15
    cP
    cC
    @0
    cG
    cI
    cL
    isperp.p
    isperp.i
    isperp.l
    @18
    @20
    @25
    @14
    cC
    @0
    wne
    @8
    @14
    @0
    cC
    @14
    @11
    cC
    cA
    wcel
    wn
    #
    @0
    cC
    wne
    @23
    wph
    @37
    @13
    foot.y
    adantr
    #
    @0
    cC
    cA
    nelne2
    syl2anc
    necomd
    #
    adantr
    tglinerflx1
    @14
    @12
    @8
    @26
    adantr
    @15
    @3
    @34
    @14
    @3
    @7
    simprl
    @14
    @3
    @34
    wb
    @8
    @14
    vv
    vu
    @1
    cA
    cP
    cG
    cI
    cL
    c.mi
    @0
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    @21
    @14
    cP
    cG
    cI
    cL
    cC
    @0
    isperp.p
    isperp.i
    isperp.l
    @21
    wph
    @19
    @13
    foot.x
    adantr
    #
    @24
    @39
    tgelrnln
    @22
    @14
    @1
    cA
    @0
    @14
    cP
    cC
    @0
    cG
    cI
    cL
    isperp.p
    isperp.i
    isperp.l
    @21
    @40
    @24
    @39
    tglinerflx2
    @23
    elind
    isperp2
    adantr
    mpbid
    @33
    @36
    cC
    @0
    @30
    cs3
    #
    @32
    wcel
    vu
    vv
    cC
    @5
    @1
    cA
    @29
    cC
    wceq
    #
    @31
    @41
    @32
    @42
    @29
    @0
    @30
    @30
    cC
    @0
    @42
    id
    #
    @42
    @0
    eqidd
    @42
    @30
    eqidd
    #
    s3eqd
    eleq1d
    @30
    @5
    wceq
    #
    @41
    @35
    @32
    @45
    cC
    @0
    @30
    @5
    cC
    @0
    @45
    cC
    eqidd
    @45
    @0
    eqidd
    @45
    id
    s3eqd
    eleq1d
    rspc2va
    syl21anc
    @15
    cC
    @6
    wcel
    @11
    @29
    @5
    @30
    cs3
    #
    @32
    wcel
    #
    vv
    cA
    wral
    vu
    @6
    wral
    #
    cC
    @5
    @0
    cs3
    #
    @32
    wcel
    #
    @15
    cP
    cC
    @5
    cG
    cI
    cL
    isperp.p
    isperp.i
    isperp.l
    @18
    @20
    @28
    @14
    cC
    @5
    wne
    @8
    @14
    @5
    cC
    @14
    @12
    @37
    @5
    cC
    wne
    @26
    @38
    @5
    cC
    cA
    nelne2
    syl2anc
    necomd
    #
    adantr
    tglinerflx1
    @14
    @11
    @8
    @23
    adantr
    @15
    @7
    @48
    @14
    @3
    @7
    simprr
    @14
    @7
    @48
    wb
    @8
    @14
    vv
    vu
    @6
    cA
    cP
    cG
    cI
    cL
    c.mi
    @5
    isperp.p
    isperp.d
    isperp.i
    isperp.l
    @21
    @14
    cP
    cG
    cI
    cL
    cC
    @5
    isperp.p
    isperp.i
    isperp.l
    @21
    @40
    @27
    @51
    tgelrnln
    @22
    @14
    @6
    cA
    @5
    @14
    cP
    cC
    @5
    cG
    cI
    cL
    isperp.p
    isperp.i
    isperp.l
    @21
    @40
    @27
    @51
    tglinerflx2
    @26
    elind
    isperp2
    adantr
    mpbid
    @47
    @50
    cC
    @5
    @30
    cs3
    #
    @32
    wcel
    vu
    vv
    cC
    @0
    @6
    cA
    @42
    @46
    @52
    @32
    @42
    @29
    @5
    @30
    @30
    cC
    @5
    @43
    @42
    @5
    eqidd
    @44
    s3eqd
    eleq1d
    @30
    @0
    wceq
    #
    @52
    @49
    @32
    @53
    cC
    @5
    @30
    @0
    cC
    @5
    @53
    cC
    eqidd
    @53
    @5
    eqidd
    @53
    id
    s3eqd
    eleq1d
    rspc2va
    syl21anc
    ragflat
    ex
    ralrimivva
    @3
    @7
    vx
    vz
    cA
    @9
    @1
    @6
    cA
    @2
    @0
    @5
    cC
    cL
    oveq2
    breq1d
    rmo4
    sylibr
    @3
    vx
    cA
    reu5
    sylanbrc
end
