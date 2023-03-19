include "cn.mm"
include "cv.mm"
include "cfv.mm"
include "cpjh.mm"
include "wcel.mm"
include "wa.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "cort.mm"
include "wrex.mm"
include "eqid.mm"
include "cch.mm"
include "cph.mm"
include "wb.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "csh.mm"
include "wss.mm"
include "chsh.mm"
include "syl.mm"
include "shocsh.mm"
include "shless.mm"
include "syl31anc.mm"
include "shscom.mm"
include "syl2anc.mm"
include "3sstr4d.mm"
include "sselda.mm"
include "syldan.mm"
include "pjpreeq.mm"
include "mpbii.mm"
include "simpld.mm"
include "fmptd.mm"

theorem chscllem1
  let wph: wff ph
  let vu: setvar u
  let cA: class A
  let cB: class B
  let vn: setvar n
  let cF: class F
  let cH: class H
  let vf: setvar f
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let vk: setvar k
  let cG: class G
  let cN: class N
  assume chscl.1: |- ( ph -> A e. CH )
  assume chscl.2: |- ( ph -> B e. CH )
  assume chscl.3: |- ( ph -> B C_ ( _|_ ` A ) )
  assume chscl.4: |- ( ph -> H : NN --> ( A +H B ) )
  assume chscl.5: |- ( ph -> H ~~>v u )
  assume chscl.6: |- F = ( n e. NN |-> ( ( projh ` A ) ` ( H ` n ) ) )

  disjoint n u
  disjoint A n
  disjoint A u
  disjoint n ph
  disjoint B n
  disjoint B u
  disjoint H n
  disjoint H u
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
  disjoint N n
  disjoint N z
  assert |- ( ph -> F : NN --> A )

  proof
    wph
    vn
    cn
    vn
    cv
    #
    cH
    cfv
    #
    cA
    cpjh
    cfv
    cfv
    #
    cA
    cF
    wph
    @0
    cn
    wcel
    #
    wa
    #
    @2
    cA
    wcel
    #
    @1
    @2
    vx
    cv
    cva
    co
    wceq
    vx
    cA
    cort
    cfv
    #
    wrex
    #
    @4
    @2
    @2
    wceq
    #
    @5
    @7
    wa
    #
    @2
    eqid
    @4
    cA
    cch
    wcel
    #
    @1
    cA
    @6
    cph
    co
    #
    wcel
    #
    @8
    @9
    wb
    wph
    @10
    @3
    chscl.1
    adantr
    wph
    @3
    @1
    cA
    cB
    cph
    co
    #
    wcel
    @12
    wph
    cn
    @13
    @0
    cH
    chscl.4
    ffvelrnda
    wph
    @13
    @11
    @1
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
    @13
    @11
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
    @14
    @15
    wss
    wph
    cB
    cch
    wcel
    @16
    chscl.2
    cB
    chsh
    syl
    #
    wph
    @18
    @17
    wph
    @10
    @18
    chscl.1
    cA
    chsh
    syl
    #
    cA
    shocsh
    syl
    #
    @20
    chscl.3
    cB
    @6
    cA
    shless
    syl31anc
    wph
    @18
    @16
    @13
    @14
    wceq
    @20
    @19
    cA
    cB
    shscom
    syl2anc
    wph
    @18
    @17
    @11
    @15
    wceq
    @20
    @21
    cA
    @6
    shscom
    syl2anc
    3sstr4d
    sselda
    syldan
    vx
    @1
    @2
    cA
    pjpreeq
    syl2anc
    mpbii
    simpld
    chscl.6
    fmptd
end
