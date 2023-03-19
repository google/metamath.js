include "cfv.mm"
include "cv.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "cort.mm"
include "wcel.mm"
include "wrex.mm"
include "cpjh.mm"
include "wa.mm"
include "cn.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "fvex.mm"
include "fvmpt.mm"
include "syl.mm"
include "eqcomd.mm"
include "cch.mm"
include "cph.mm"
include "wb.mm"
include "csh.mm"
include "wss.mm"
include "chsh.mm"
include "shocsh.mm"
include "shless.mm"
include "syl31anc.mm"
include "shscom.mm"
include "syl2anc.mm"
include "3sstr4d.mm"
include "ffvelrnd.mm"
include "sseldd.mm"
include "pjpreeq.mm"
include "mpbid.mm"
include "simprd.mm"
include "adantr.mm"
include "cin.mm"
include "c0h.mm"
include "ocin.mm"
include "chscllem1.mm"
include "simprl.mm"
include "simprr.mm"
include "eqtr3d.mm"
include "shuni.mm"
include "simpld.mm"
include "rexlimddv.mm"

theorem chscllem3
  let wph: wff ph
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vn: setvar n
  let cF: class F
  let cH: class H
  let cN: class N
  let vf: setvar f
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  let cG: class G
  assume chscl.1: |- ( ph -> A e. CH )
  assume chscl.2: |- ( ph -> B e. CH )
  assume chscl.3: |- ( ph -> B C_ ( _|_ ` A ) )
  assume chscl.4: |- ( ph -> H : NN --> ( A +H B ) )
  assume chscl.5: |- ( ph -> H ~~>v u )
  assume chscl.6: |- F = ( n e. NN |-> ( ( projh ` A ) ` ( H ` n ) ) )
  assume chscllem3.7: |- ( ph -> N e. NN )
  assume chscllem3.8: |- ( ph -> C e. A )
  assume chscllem3.9: |- ( ph -> D e. B )
  assume chscllem3.10: |- ( ph -> ( H ` N ) = ( C +h D ) )

  disjoint n u
  disjoint A n
  disjoint A u
  disjoint n ph
  disjoint B n
  disjoint B u
  disjoint H n
  disjoint H u
  disjoint N n
  disjoint f j
  disjoint f n
  disjoint f u
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint j n
  disjoint j u
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint A j
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint C z
  disjoint j k
  disjoint F j
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint F k
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint f k
  disjoint f ph
  disjoint j ph
  disjoint k n
  disjoint k ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint B f
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint G k
  disjoint G x
  disjoint G y
  disjoint H j
  disjoint k u
  disjoint H k
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint N z
  assert |- ( ph -> C = ( F ` N ) )

  proof
    wph
    cN
    cH
    cfv
    #
    cN
    cF
    cfv
    #
    vz
    cv
    #
    cva
    co
    #
    wceq
    #
    cC
    @1
    wceq
    #
    vz
    cA
    cort
    cfv
    #
    wph
    @1
    cA
    wcel
    #
    @4
    vz
    @6
    wrex
    #
    wph
    @0
    cA
    cpjh
    cfv
    #
    cfv
    #
    @1
    wceq
    #
    @7
    @8
    wa
    #
    wph
    @1
    @10
    wph
    cN
    cn
    wcel
    @1
    @10
    wceq
    chscllem3.7
    vn
    cN
    vn
    cv
    #
    cH
    cfv
    #
    @9
    cfv
    @10
    cn
    cF
    @13
    cN
    wceq
    @14
    @0
    @9
    @13
    cN
    cH
    fveq2
    fveq2d
    chscl.6
    @0
    @9
    fvex
    fvmpt
    syl
    eqcomd
    wph
    cA
    cch
    wcel
    #
    @0
    cA
    @6
    cph
    co
    #
    wcel
    @11
    @12
    wb
    chscl.1
    wph
    cA
    cB
    cph
    co
    #
    @16
    @0
    wph
    cB
    cA
    cph
    co
    #
    @6
    cA
    cph
    co
    #
    @17
    @16
    wph
    cB
    csh
    wcel
    #
    @6
    csh
    wcel
    #
    cA
    csh
    wcel
    #
    cB
    @6
    wss
    #
    @18
    @19
    wss
    wph
    cB
    cch
    wcel
    @20
    chscl.2
    cB
    chsh
    syl
    #
    wph
    @22
    @21
    wph
    @15
    @22
    chscl.1
    cA
    chsh
    syl
    #
    cA
    shocsh
    syl
    #
    @25
    chscl.3
    cB
    @6
    cA
    shless
    syl31anc
    wph
    @22
    @20
    @17
    @18
    wceq
    @25
    @24
    cA
    cB
    shscom
    syl2anc
    wph
    @22
    @21
    @16
    @19
    wceq
    @25
    @26
    cA
    @6
    shscom
    syl2anc
    3sstr4d
    wph
    cn
    @17
    cN
    cH
    chscl.4
    chscllem3.7
    ffvelrnd
    sseldd
    vz
    @0
    @1
    cA
    pjpreeq
    syl2anc
    mpbid
    simprd
    wph
    @2
    @6
    wcel
    #
    @4
    wa
    #
    wa
    #
    @5
    cD
    @2
    wceq
    @29
    cC
    cD
    @1
    @2
    cA
    @6
    wph
    @22
    @28
    @25
    adantr
    wph
    @21
    @28
    @26
    adantr
    wph
    cA
    @6
    cin
    c0h
    wceq
    #
    @28
    wph
    @22
    @30
    @25
    cA
    ocin
    syl
    adantr
    wph
    cC
    cA
    wcel
    @28
    chscllem3.8
    adantr
    @29
    cB
    @6
    cD
    wph
    @23
    @28
    chscl.3
    adantr
    wph
    cD
    cB
    wcel
    @28
    chscllem3.9
    adantr
    sseldd
    wph
    @7
    @28
    wph
    cn
    cA
    cN
    cF
    wph
    vu
    cA
    cB
    vn
    cF
    cH
    chscl.1
    chscl.2
    chscl.3
    chscl.4
    chscl.5
    chscl.6
    chscllem1
    chscllem3.7
    ffvelrnd
    adantr
    wph
    @27
    @4
    simprl
    @29
    @0
    cC
    cD
    cva
    co
    #
    @3
    wph
    @0
    @31
    wceq
    @28
    chscllem3.10
    adantr
    wph
    @27
    @4
    simprr
    eqtr3d
    shuni
    simpld
    rexlimddv
end
