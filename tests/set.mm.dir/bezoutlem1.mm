include "cabs.mm"
include "cfv.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "cz.mm"
include "wrex.mm"
include "cc0.mm"
include "wne.mm"
include "cn.mm"
include "wcel.mm"
include "fveq2.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "rexbidv.mm"
include "cr.mm"
include "zre.mm"
include "cneg.mm"
include "c1.mm"
include "1z.mm"
include "ax-1rid.mm"
include "eqcomd.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "sylancr.mm"
include "eqeq1.mm"
include "syl5ibrcom.mm"
include "neg1z.mm"
include "recn.mm"
include "mulm1d.mm"
include "cc.mm"
include "neg1cn.mm"
include "mulcom.mm"
include "eqtr3d.mm"
include "absor.mm"
include "mpjaod.mm"
include "syl.mm"
include "vtoclga.mm"
include "wa.mm"
include "zcnd.mm"
include "adantr.mm"
include "mul01d.mm"
include "oveq2d.mm"
include "zcn.mm"
include "mulcl.mm"
include "syl2an.mm"
include "addid1d.mm"
include "eqtrd.mm"
include "0z.mm"
include "mpan.mm"
include "syl6bir.mm"
include "reximdva.mm"
include "mpd.mm"
include "wi.mm"
include "nnabscl.mm"
include "ex.mm"
include "2rexbidv.mm"
include "elrab2.mm"
include "simplbi2com.mm"
include "sylsyld.mm"

theorem bezoutlem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cM: class M
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let cG: class G
  let cC: class C
  assume bezout.1: |- M = { z e. NN | E. x e. ZZ E. y e. ZZ z = ( ( A x. x ) + ( B x. y ) ) }
  assume bezout.3: |- ( ph -> A e. ZZ )
  assume bezout.4: |- ( ph -> B e. ZZ )

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint G s
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint G t
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint G u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint G v
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint M s
  disjoint M t
  disjoint M u
  disjoint M v
  disjoint ph s
  disjoint ph t
  disjoint ph u
  disjoint ph v
  disjoint C s
  disjoint C t
  disjoint C u
  disjoint C v
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint B s
  disjoint B t
  disjoint B u
  disjoint B v
  assert |- ( ph -> ( A =/= 0 -> ( abs ` A ) e. M ) )

  proof
    wph
    cA
    cabs
    cfv
    #
    cA
    vx
    cv
    #
    cmul
    co
    #
    cB
    vy
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vy
    cz
    wrex
    #
    vx
    cz
    wrex
    #
    cA
    cc0
    wne
    #
    @0
    cn
    wcel
    #
    @0
    cM
    wcel
    #
    wph
    @0
    @2
    wceq
    #
    vx
    cz
    wrex
    #
    @8
    wph
    cA
    cz
    wcel
    #
    @13
    bezout.3
    vz
    cv
    #
    cabs
    cfv
    #
    @15
    @1
    cmul
    co
    #
    wceq
    #
    vx
    cz
    wrex
    #
    @13
    vz
    cA
    cz
    @15
    cA
    wceq
    #
    @18
    @12
    vx
    cz
    @20
    @16
    @0
    @17
    @2
    @15
    cA
    cabs
    fveq2
    @15
    cA
    @1
    cmul
    oveq1
    eqeq12d
    rexbidv
    @15
    cz
    wcel
    @15
    cr
    wcel
    #
    @19
    @15
    zre
    @21
    @16
    @15
    wceq
    #
    @19
    @16
    @15
    cneg
    #
    wceq
    #
    @21
    @19
    @22
    @15
    @17
    wceq
    #
    vx
    cz
    wrex
    #
    @21
    c1
    cz
    wcel
    @15
    @15
    c1
    cmul
    co
    #
    wceq
    #
    @26
    1z
    @21
    @27
    @15
    @15
    ax-1rid
    eqcomd
    @25
    @28
    vx
    c1
    cz
    @1
    c1
    wceq
    @17
    @27
    @15
    @1
    c1
    @15
    cmul
    oveq2
    eqeq2d
    rspcev
    sylancr
    @22
    @18
    @25
    vx
    cz
    @16
    @15
    @17
    eqeq1
    rexbidv
    syl5ibrcom
    @21
    @19
    @24
    @23
    @17
    wceq
    #
    vx
    cz
    wrex
    #
    @21
    c1
    cneg
    #
    cz
    wcel
    @23
    @15
    @31
    cmul
    co
    #
    wceq
    #
    @30
    neg1z
    @21
    @31
    @15
    cmul
    co
    #
    @23
    @32
    @21
    @15
    @15
    recn
    #
    mulm1d
    @21
    @31
    cc
    wcel
    @15
    cc
    wcel
    @34
    @32
    wceq
    neg1cn
    @35
    @31
    @15
    mulcom
    sylancr
    eqtr3d
    @29
    @33
    vx
    @31
    cz
    @1
    @31
    wceq
    @17
    @32
    @23
    @1
    @31
    @15
    cmul
    oveq2
    eqeq2d
    rspcev
    sylancr
    @24
    @18
    @29
    vx
    cz
    @16
    @23
    @17
    eqeq1
    rexbidv
    syl5ibrcom
    @15
    absor
    mpjaod
    syl
    vtoclga
    syl
    wph
    @12
    @7
    vx
    cz
    wph
    @1
    cz
    wcel
    #
    wa
    #
    @12
    @0
    @2
    cB
    cc0
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    @7
    @37
    @39
    @2
    @0
    @37
    @39
    @2
    cc0
    caddc
    co
    @2
    @37
    @38
    cc0
    @2
    caddc
    @37
    cB
    wph
    cB
    cc
    wcel
    @36
    wph
    cB
    bezout.4
    zcnd
    adantr
    mul01d
    oveq2d
    @37
    @2
    wph
    cA
    cc
    wcel
    @1
    cc
    wcel
    @2
    cc
    wcel
    @36
    wph
    cA
    bezout.3
    zcnd
    @1
    zcn
    cA
    @1
    mulcl
    syl2an
    addid1d
    eqtrd
    eqeq2d
    cc0
    cz
    wcel
    @40
    @7
    0z
    @6
    @40
    vy
    cc0
    cz
    @3
    cc0
    wceq
    #
    @5
    @39
    @0
    @41
    @4
    @38
    @2
    caddc
    @3
    cc0
    cB
    cmul
    oveq2
    oveq2d
    eqeq2d
    rspcev
    mpan
    syl6bir
    reximdva
    mpd
    wph
    @14
    @9
    @10
    wi
    bezout.3
    @14
    @9
    @10
    cA
    nnabscl
    ex
    syl
    @11
    @10
    @8
    @15
    @5
    wceq
    #
    vy
    cz
    wrex
    vx
    cz
    wrex
    @8
    vz
    @0
    cn
    cM
    @15
    @0
    wceq
    @42
    @6
    vx
    vy
    cz
    cz
    @15
    @0
    @5
    eqeq1
    2rexbidv
    bezout.1
    elrab2
    simplbi2com
    sylsyld
end
