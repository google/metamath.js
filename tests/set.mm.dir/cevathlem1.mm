include "cmul.mm"
include "co.mm"
include "cc.mm"
include "wcel.mm"
include "simp2d.mm"
include "simp3d.mm"
include "mulcld.mm"
include "simp1d.mm"
include "cc0.mm"
include "wne.mm"
include "mulne0d.mm"
include "wceq.mm"
include "oveq12d.mm"
include "mul4d.mm"
include "3eqtr3d.mm"
include "mul32d.mm"
include "mulcomd.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "eqtr4d.mm"
include "mulcanad.mm"

theorem cevathlem1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let vk: setvar k
  let vx: setvar x
  assume cevathlem1.a: |- ( ph -> ( A e. CC /\ B e. CC /\ C e. CC ) )
  assume cevathlem1.b: |- ( ph -> ( D e. CC /\ E e. CC /\ F e. CC ) )
  assume cevathlem1.c: |- ( ph -> ( G e. CC /\ H e. CC /\ K e. CC ) )
  assume cevathlem1.d: |- ( ph -> ( A =/= 0 /\ E =/= 0 /\ C =/= 0 ) )
  assume cevathlem1.e: |- ( ph -> ( ( A x. B ) = ( C x. D ) /\ ( E x. F ) = ( A x. G ) /\ ( C x. H ) = ( E x. K ) ) )


  assert |- ( ph -> ( ( B x. F ) x. H ) = ( ( D x. G ) x. K ) )

  proof
    wph
    cB
    cF
    cmul
    co
    #
    cH
    cmul
    co
    #
    cD
    cG
    cmul
    co
    #
    cK
    cmul
    co
    #
    cA
    cE
    cmul
    co
    #
    cC
    cmul
    co
    #
    wph
    @0
    cH
    wph
    cB
    cF
    wph
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    cC
    cc
    wcel
    #
    cevathlem1.a
    simp2d
    #
    wph
    cD
    cc
    wcel
    #
    cE
    cc
    wcel
    #
    cF
    cc
    wcel
    #
    cevathlem1.b
    simp3d
    #
    mulcld
    #
    wph
    cG
    cc
    wcel
    #
    cH
    cc
    wcel
    #
    cK
    cc
    wcel
    #
    cevathlem1.c
    simp2d
    #
    mulcld
    wph
    @2
    cK
    wph
    cD
    cG
    wph
    @10
    @11
    @12
    cevathlem1.b
    simp1d
    #
    wph
    @15
    @16
    @17
    cevathlem1.c
    simp1d
    #
    mulcld
    #
    wph
    @15
    @16
    @17
    cevathlem1.c
    simp3d
    #
    mulcld
    wph
    @4
    cC
    wph
    cA
    cE
    wph
    @6
    @7
    @8
    cevathlem1.a
    simp1d
    #
    wph
    @10
    @11
    @12
    cevathlem1.b
    simp2d
    #
    mulcld
    #
    wph
    @6
    @7
    @8
    cevathlem1.a
    simp3d
    #
    mulcld
    wph
    @4
    cC
    @25
    @26
    wph
    cA
    cE
    @23
    @24
    wph
    cA
    cc0
    wne
    #
    cE
    cc0
    wne
    #
    cC
    cc0
    wne
    #
    cevathlem1.d
    simp1d
    wph
    @27
    @28
    @29
    cevathlem1.d
    simp2d
    mulne0d
    wph
    @27
    @28
    @29
    cevathlem1.d
    simp3d
    mulne0d
    wph
    @5
    @1
    cmul
    co
    #
    cC
    cA
    cmul
    co
    #
    cE
    cmul
    co
    #
    @3
    cmul
    co
    #
    @5
    @3
    cmul
    co
    wph
    @4
    @0
    cmul
    co
    #
    cC
    cH
    cmul
    co
    #
    cmul
    co
    @31
    @2
    cmul
    co
    #
    cE
    cK
    cmul
    co
    #
    cmul
    co
    @30
    @33
    wph
    @34
    @36
    @35
    @37
    cmul
    wph
    cA
    cB
    cmul
    co
    #
    cE
    cF
    cmul
    co
    #
    cmul
    co
    cC
    cD
    cmul
    co
    #
    cA
    cG
    cmul
    co
    #
    cmul
    co
    @34
    @36
    wph
    @38
    @40
    @39
    @41
    cmul
    wph
    @38
    @40
    wceq
    #
    @39
    @41
    wceq
    #
    @35
    @37
    wceq
    #
    cevathlem1.e
    simp1d
    wph
    @42
    @43
    @44
    cevathlem1.e
    simp2d
    oveq12d
    wph
    cA
    cB
    cE
    cF
    @23
    @9
    @24
    @13
    mul4d
    wph
    cC
    cD
    cA
    cG
    @26
    @19
    @23
    @20
    mul4d
    3eqtr3d
    wph
    @42
    @43
    @44
    cevathlem1.e
    simp3d
    oveq12d
    wph
    @4
    @0
    cC
    cH
    @25
    @14
    @26
    @18
    mul4d
    wph
    @31
    @2
    cE
    cK
    wph
    cC
    cA
    @26
    @23
    mulcld
    @21
    @24
    @22
    mul4d
    3eqtr3d
    wph
    @5
    @32
    @3
    cmul
    wph
    @5
    cA
    cC
    cmul
    co
    #
    cE
    cmul
    co
    @32
    wph
    cA
    cE
    cC
    @23
    @24
    @26
    mul32d
    wph
    @45
    @31
    cE
    cmul
    wph
    cA
    cC
    @23
    @26
    mulcomd
    oveq1d
    eqtrd
    oveq1d
    eqtr4d
    mulcanad
end
