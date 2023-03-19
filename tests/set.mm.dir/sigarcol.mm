include "cmin.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "cv.mm"
include "cmul.mm"
include "caddc.mm"
include "cr.mm"
include "wrex.mm"
include "wa.mm"
include "cdiv.mm"
include "wcel.mm"
include "cc.mm"
include "w3a.mm"
include "simp2d.mm"
include "simp3d.mm"
include "simp1d.mm"
include "3jca.mm"
include "adantr.mm"
include "wn.mm"
include "sigarperm.mm"
include "syl.mm"
include "eqtrd.mm"
include "eqeq1d.mm"
include "biimpa.mm"
include "sigardiv.mm"
include "subcld.mm"
include "neqned.mm"
include "subne0d.mm"
include "divcan1d.mm"
include "oveq2d.mm"
include "pncan3d.mm"
include "eqtr2d.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ex.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "oveq1d.mm"
include "simp2.mm"
include "recnd.mm"
include "mulcld.mm"
include "pncan2d.mm"
include "mulcomd.mm"
include "cneg.mm"
include "sigarac.mm"
include "sigarls.mm"
include "syl3anc.mm"
include "sigarid.mm"
include "mul02d.mm"
include "3eqtrd.mm"
include "negeqd.mm"
include "neg0.mm"
include "a1i.mm"
include "rexlimdv3a.mm"
include "impbid.mm"

theorem sigarcol
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cG: class G
  let vk: setvar k
  assume sigarcol.sigar: |- G = ( x e. CC , y e. CC |-> ( Im ` ( ( * ` x ) x. y ) ) )
  assume sigarcol.a: |- ( ph -> ( A e. CC /\ B e. CC /\ C e. CC ) )
  assume sigarcol.b: |- ( ph -> -. A = B )

  disjoint t x
  disjoint t y
  disjoint A t
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B t
  disjoint B x
  disjoint B y
  disjoint C t
  disjoint C x
  disjoint C y
  disjoint G t
  disjoint ph t
  disjoint k x
  assert |- ( ph -> ( ( ( A - C ) G ( B - C ) ) = 0 <-> E. t e. RR C = ( B + ( t x. ( A - B ) ) ) ) )

  proof
    wph
    cA
    cC
    cmin
    co
    cB
    cC
    cmin
    co
    cG
    co
    #
    cc0
    wceq
    #
    cC
    cB
    vt
    cv
    #
    cA
    cB
    cmin
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vt
    cr
    wrex
    #
    wph
    @1
    @7
    wph
    @1
    wa
    #
    cC
    cB
    cmin
    co
    #
    @3
    cdiv
    co
    #
    cr
    wcel
    cC
    cB
    @10
    @3
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    @7
    @8
    vx
    vy
    cB
    cC
    cA
    cG
    sigarcol.sigar
    wph
    cB
    cc
    wcel
    #
    cC
    cc
    wcel
    #
    cA
    cc
    wcel
    #
    w3a
    #
    @1
    wph
    @14
    @15
    @16
    wph
    @16
    @14
    @15
    sigarcol.a
    simp2d
    #
    wph
    @16
    @14
    @15
    sigarcol.a
    simp3d
    #
    wph
    @16
    @14
    @15
    sigarcol.a
    simp1d
    #
    3jca
    #
    adantr
    wph
    cA
    cB
    wceq
    wn
    @1
    sigarcol.b
    adantr
    #
    wph
    @1
    @9
    @3
    cG
    co
    #
    cc0
    wceq
    wph
    @0
    @23
    cc0
    wph
    @0
    cB
    cA
    cmin
    co
    cC
    cA
    cmin
    co
    cG
    co
    #
    @23
    wph
    @16
    @14
    @15
    w3a
    @0
    @24
    wceq
    sigarcol.a
    vx
    vy
    cA
    cB
    cC
    cG
    sigarcol.sigar
    sigarperm
    syl
    wph
    @17
    @24
    @23
    wceq
    @21
    vx
    vy
    cB
    cC
    cA
    cG
    sigarcol.sigar
    sigarperm
    syl
    eqtrd
    #
    eqeq1d
    biimpa
    sigardiv
    @8
    @12
    cB
    @9
    caddc
    co
    cC
    @8
    @11
    @9
    cB
    caddc
    @8
    @9
    @3
    wph
    @9
    cc
    wcel
    @1
    wph
    cC
    cB
    @19
    @18
    subcld
    adantr
    wph
    @3
    cc
    wcel
    #
    @1
    wph
    cA
    cB
    @20
    @18
    subcld
    adantr
    @8
    cA
    cB
    wph
    @16
    @1
    @20
    adantr
    wph
    @14
    @1
    @18
    adantr
    #
    @8
    cA
    cB
    @22
    neqned
    subne0d
    divcan1d
    oveq2d
    @8
    cB
    cC
    @27
    wph
    @15
    @1
    @19
    adantr
    pncan3d
    eqtr2d
    @6
    @13
    vt
    @10
    cr
    @2
    @10
    wceq
    #
    @5
    @12
    cC
    @28
    @4
    @11
    cB
    caddc
    @2
    @10
    @3
    cmul
    oveq1
    oveq2d
    eqeq2d
    rspcev
    syl2anc
    ex
    wph
    @6
    @1
    vt
    cr
    wph
    @2
    cr
    wcel
    #
    @6
    w3a
    #
    @0
    @23
    @3
    @2
    cmul
    co
    #
    @3
    cG
    co
    #
    cc0
    wph
    @29
    @0
    @23
    wceq
    @6
    @25
    3ad2ant1
    @30
    @23
    @4
    @3
    cG
    co
    @32
    @30
    @9
    @4
    @3
    cG
    @30
    @9
    @5
    cB
    cmin
    co
    @4
    @30
    cC
    @5
    cB
    cmin
    wph
    @29
    @6
    simp3
    oveq1d
    @30
    cB
    @4
    wph
    @29
    @14
    @6
    @18
    3ad2ant1
    #
    @30
    @2
    @3
    @30
    @2
    wph
    @29
    @6
    simp2
    #
    recnd
    #
    @30
    cA
    cB
    wph
    @29
    @16
    @6
    @20
    3ad2ant1
    @33
    subcld
    #
    mulcld
    pncan2d
    eqtrd
    oveq1d
    @30
    @4
    @31
    @3
    cG
    @30
    @2
    @3
    @35
    @36
    mulcomd
    oveq1d
    eqtrd
    @30
    @32
    @3
    @31
    cG
    co
    #
    cneg
    #
    cc0
    cneg
    #
    cc0
    @30
    @31
    cc
    wcel
    @26
    @32
    @38
    wceq
    @30
    @3
    @2
    @36
    @35
    mulcld
    @36
    vx
    vy
    @31
    @3
    cG
    sigarcol.sigar
    sigarac
    syl2anc
    @30
    @37
    cc0
    @30
    @37
    @3
    @3
    cG
    co
    #
    @2
    cmul
    co
    #
    cc0
    @2
    cmul
    co
    cc0
    @30
    @26
    @26
    @29
    @37
    @41
    wceq
    @36
    @36
    @34
    vx
    vy
    @3
    @3
    @2
    cG
    sigarcol.sigar
    sigarls
    syl3anc
    @30
    @40
    cc0
    @2
    cmul
    @30
    @26
    @40
    cc0
    wceq
    @36
    vx
    vy
    @3
    cG
    sigarcol.sigar
    sigarid
    syl
    oveq1d
    @30
    @2
    @35
    mul02d
    3eqtrd
    negeqd
    @39
    cc0
    wceq
    @30
    neg0
    a1i
    3eqtrd
    3eqtrd
    rexlimdv3a
    impbid
end
