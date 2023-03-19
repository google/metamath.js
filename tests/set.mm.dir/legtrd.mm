include "co.mm"
include "wbr.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cs3.mm"
include "ccgrg.mm"
include "cfv.mm"
include "clng.mm"
include "eqid.mm"
include "cstrkg.mm"
include "ad4antr.mm"
include "simp-4r.mm"
include "simplr.mm"
include "simpllr.mm"
include "simpld.mm"
include "btwncolg3.mm"
include "simprr.mm"
include "lnext.mm"
include "ad2antrr.mm"
include "ad6antr.mm"
include "simpr.mm"
include "cgr3swap23.mm"
include "tgbtwnxfr.mm"
include "tgbtwnexch.mm"
include "simp-5r.mm"
include "simprd.mm"
include "cgr3simp1.mm"
include "eqtrd.mm"
include "jca.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"
include "legov.mm"
include "mpbid.mm"
include "r19.29a.mm"
include "mpbird.mm"

theorem legtrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let c.le: class .<_
  let c.mi: class .-
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume legval.p: |- P = ( Base ` G )
  assume legval.d: |- .- = ( dist ` G )
  assume legval.i: |- I = ( Itv ` G )
  assume legval.l: |- .<_ = ( leG ` G )
  assume legval.g: |- ( ph -> G e. TarskiG )
  assume legid.a: |- ( ph -> A e. P )
  assume legid.b: |- ( ph -> B e. P )
  assume legtrd.c: |- ( ph -> C e. P )
  assume legtrd.d: |- ( ph -> D e. P )
  assume legtrd.e: |- ( ph -> E e. P )
  assume legtrd.f: |- ( ph -> F e. P )
  assume legtrd.1: |- ( ph -> ( A .- B ) .<_ ( C .- D ) )
  assume legtrd.2: |- ( ph -> ( C .- D ) .<_ ( E .- F ) )


  assert |- ( ph -> ( A .- B ) .<_ ( E .- F ) )

  proof
    wph
    cA
    cB
    c.mi
    co
    #
    cE
    cF
    c.mi
    co
    #
    c.le
    wbr
    vz
    cv
    #
    cE
    cF
    cI
    co
    #
    wcel
    #
    @0
    cE
    @2
    c.mi
    co
    #
    wceq
    #
    wa
    #
    vz
    cP
    wrex
    #
    wph
    vx
    cv
    #
    cC
    cD
    cI
    co
    wcel
    #
    @0
    cC
    @9
    c.mi
    co
    #
    wceq
    #
    wa
    #
    @8
    vx
    cP
    wph
    @9
    cP
    wcel
    #
    wa
    #
    @13
    wa
    #
    vy
    cv
    #
    @3
    wcel
    #
    cC
    cD
    c.mi
    co
    #
    cE
    @17
    c.mi
    co
    wceq
    #
    wa
    #
    @8
    vy
    cP
    @16
    @17
    cP
    wcel
    #
    wa
    #
    @21
    wa
    #
    cC
    cD
    @9
    cs3
    cE
    @17
    @2
    cs3
    cG
    ccgrg
    cfv
    #
    wbr
    #
    vz
    cP
    wrex
    @8
    @24
    cE
    @17
    cP
    @25
    cG
    cI
    cG
    clng
    cfv
    #
    c.mi
    cC
    cD
    @9
    vz
    legval.p
    @27
    eqid
    #
    legval.i
    wph
    cG
    cstrkg
    wcel
    #
    @14
    @13
    @22
    @21
    legval.g
    ad4antr
    #
    wph
    cC
    cP
    wcel
    #
    @14
    @13
    @22
    @21
    legtrd.c
    ad4antr
    #
    wph
    cD
    cP
    wcel
    #
    @14
    @13
    @22
    @21
    legtrd.d
    ad4antr
    #
    wph
    @14
    @13
    @22
    @21
    simp-4r
    #
    @25
    eqid
    #
    wph
    cE
    cP
    wcel
    #
    @14
    @13
    @22
    @21
    legtrd.e
    ad4antr
    #
    @16
    @22
    @21
    simplr
    legval.d
    @24
    cP
    cG
    cI
    @27
    cC
    @9
    cD
    legval.p
    @28
    legval.i
    @30
    @32
    @35
    @34
    @24
    @10
    @12
    @15
    @13
    @22
    @21
    simpllr
    simpld
    #
    btwncolg3
    @23
    @18
    @20
    simprr
    lnext
    @24
    @26
    @7
    vz
    cP
    @24
    @2
    cP
    wcel
    #
    wa
    #
    @26
    @7
    @41
    @26
    wa
    #
    @4
    @6
    @42
    cE
    @2
    @17
    cF
    cP
    cG
    cI
    c.mi
    legval.p
    legval.d
    legval.i
    @24
    @29
    @40
    @26
    @30
    ad2antrr
    #
    @24
    @37
    @40
    @26
    @38
    ad2antrr
    #
    @24
    @40
    @26
    simplr
    #
    @16
    @22
    @21
    @40
    @26
    simp-4r
    #
    wph
    cF
    cP
    wcel
    @14
    @13
    @22
    @21
    @40
    @26
    legtrd.f
    ad6antr
    @42
    cC
    @9
    cD
    cE
    cP
    @25
    @2
    @17
    cG
    cI
    c.mi
    legval.p
    legval.d
    legval.i
    @36
    @43
    @24
    @31
    @40
    @26
    @32
    ad2antrr
    #
    @24
    @14
    @40
    @26
    @35
    ad2antrr
    #
    @24
    @33
    @40
    @26
    @34
    ad2antrr
    #
    @44
    @45
    @46
    @42
    cC
    cD
    @9
    cE
    cP
    @25
    @17
    @2
    cG
    cI
    c.mi
    legval.p
    legval.d
    legval.i
    @36
    @43
    @47
    @49
    @48
    @44
    @46
    @45
    @41
    @26
    simpr
    cgr3swap23
    #
    @24
    @10
    @40
    @26
    @39
    ad2antrr
    tgbtwnxfr
    @42
    @18
    @20
    @23
    @21
    @40
    @26
    simpllr
    simpld
    tgbtwnexch
    @42
    @0
    @11
    @5
    @42
    @10
    @12
    @15
    @13
    @22
    @21
    @40
    @26
    simp-5r
    simprd
    @42
    cC
    @9
    cD
    cE
    cP
    @25
    @2
    @17
    cG
    cI
    c.mi
    legval.p
    legval.d
    legval.i
    @36
    @43
    @47
    @48
    @49
    @44
    @45
    @46
    @50
    cgr3simp1
    eqtrd
    jca
    ex
    reximdva
    mpd
    wph
    @21
    vy
    cP
    wrex
    #
    @14
    @13
    wph
    @19
    @1
    c.le
    wbr
    @51
    legtrd.2
    wph
    vy
    cC
    cD
    cE
    cF
    cP
    cG
    cI
    c.le
    c.mi
    legval.p
    legval.d
    legval.i
    legval.l
    legval.g
    legtrd.c
    legtrd.d
    legtrd.e
    legtrd.f
    legov
    mpbid
    ad2antrr
    r19.29a
    wph
    @0
    @19
    c.le
    wbr
    @13
    vx
    cP
    wrex
    legtrd.1
    wph
    vx
    cA
    cB
    cC
    cD
    cP
    cG
    cI
    c.le
    c.mi
    legval.p
    legval.d
    legval.i
    legval.l
    legval.g
    legid.a
    legid.b
    legtrd.c
    legtrd.d
    legov
    mpbid
    r19.29a
    wph
    vz
    cA
    cB
    cE
    cF
    cP
    cG
    cI
    c.le
    c.mi
    legval.p
    legval.d
    legval.i
    legval.l
    legval.g
    legid.a
    legid.b
    legtrd.e
    legtrd.f
    legov
    mpbird
end
