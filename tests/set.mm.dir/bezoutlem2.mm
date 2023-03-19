include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "c1.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wcel.mm"
include "cn.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "cz.mm"
include "wrex.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "nnuz.mm"
include "sseqtri.mm"
include "cc0.mm"
include "cabs.mm"
include "bezoutlem1.mm"
include "ne0i.mm"
include "syl6.mm"
include "eqid.mm"
include "rexcom.mm"
include "wa.mm"
include "cc.mm"
include "zcnd.mm"
include "adantr.mm"
include "zcn.mm"
include "ad2antll.mm"
include "mulcld.mm"
include "ad2antrl.mm"
include "addcomd.mm"
include "eqeq2d.mm"
include "2rexbidva.mm"
include "syl5bb.mm"
include "rabbidv.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "sylibrd.mm"
include "wn.mm"
include "wo.mm"
include "neorian.mm"
include "sylibr.mm"
include "mpjaod.mm"
include "infssuzcl.mm"
include "sylancr.mm"
include "syl5eqel.mm"

theorem bezoutlem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cG: class G
  let cM: class M
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let cC: class C
  assume bezout.1: |- M = { z e. NN | E. x e. ZZ E. y e. ZZ z = ( ( A x. x ) + ( B x. y ) ) }
  assume bezout.3: |- ( ph -> A e. ZZ )
  assume bezout.4: |- ( ph -> B e. ZZ )
  assume bezout.2: |- G = inf ( M , RR , < )
  assume bezout.5: |- ( ph -> -. ( A = 0 /\ B = 0 ) )

  disjoint x y
  disjoint x z
  disjoint G x
  disjoint y z
  disjoint G y
  disjoint G z
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
  assert |- ( ph -> G e. M )

  proof
    wph
    cG
    cM
    cr
    clt
    cinf
    #
    cM
    bezout.2
    wph
    cM
    c1
    cuz
    cfv
    #
    wss
    cM
    c0
    wne
    #
    @0
    cM
    wcel
    cM
    cn
    @1
    cM
    vz
    cv
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
    vx
    cz
    wrex
    #
    vz
    cn
    crab
    #
    cn
    bezout.1
    @10
    vz
    cn
    ssrab2
    eqsstri
    nnuz
    sseqtri
    wph
    cA
    cc0
    wne
    #
    @2
    cB
    cc0
    wne
    #
    wph
    @12
    cA
    cabs
    cfv
    #
    cM
    wcel
    @2
    wph
    vx
    vy
    vz
    cA
    cB
    cM
    bezout.1
    bezout.3
    bezout.4
    bezoutlem1
    cM
    @14
    ne0i
    syl6
    wph
    @13
    cB
    cabs
    cfv
    #
    cM
    wcel
    #
    @2
    wph
    @13
    @15
    @3
    @7
    @5
    caddc
    co
    #
    wceq
    #
    vx
    cz
    wrex
    vy
    cz
    wrex
    #
    vz
    cn
    crab
    #
    wcel
    @16
    wph
    vy
    vx
    vz
    cB
    cA
    @20
    @20
    eqid
    bezout.4
    bezout.3
    bezoutlem1
    wph
    cM
    @20
    @15
    wph
    cM
    @11
    @20
    bezout.1
    wph
    @10
    @19
    vz
    cn
    @10
    @9
    vx
    cz
    wrex
    vy
    cz
    wrex
    wph
    @19
    @9
    vx
    vy
    cz
    cz
    rexcom
    wph
    @9
    @18
    vy
    vx
    cz
    cz
    wph
    @6
    cz
    wcel
    #
    @4
    cz
    wcel
    #
    wa
    #
    wa
    #
    @8
    @17
    @3
    @24
    @5
    @7
    @24
    cA
    @4
    wph
    cA
    cc
    wcel
    @23
    wph
    cA
    bezout.3
    zcnd
    adantr
    @22
    @4
    cc
    wcel
    wph
    @21
    @4
    zcn
    ad2antll
    mulcld
    @24
    cB
    @6
    wph
    cB
    cc
    wcel
    @23
    wph
    cB
    bezout.4
    zcnd
    adantr
    @21
    @6
    cc
    wcel
    wph
    @22
    @6
    zcn
    ad2antrl
    mulcld
    addcomd
    eqeq2d
    2rexbidva
    syl5bb
    rabbidv
    syl5eq
    eleq2d
    sylibrd
    cM
    @15
    ne0i
    syl6
    wph
    cA
    cc0
    wceq
    cB
    cc0
    wceq
    wa
    wn
    @12
    @13
    wo
    bezout.5
    cA
    cc0
    cB
    cc0
    neorian
    sylibr
    mpjaod
    cM
    c1
    infssuzcl
    sylancr
    syl5eqel
end
