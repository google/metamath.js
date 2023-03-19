include "cmpt.mm"
include "clsp.mm"
include "cfv.mm"
include "cmbf.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cli.mm"
include "wbr.mm"
include "wceq.mm"
include "cr.mm"
include "anass1rs.mm"
include "eqid.mm"
include "fmptd.mm"
include "cz.mm"
include "cdm.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "adantr.mm"
include "climrel.mm"
include "releldmi.mm"
include "syl.mm"
include "climcau.mm"
include "syl2anc.mm"
include "caurcvg.mm"
include "climuni.mm"
include "mpteq2dva.mm"
include "cpnf.mm"
include "cico.mm"
include "cima.mm"
include "cxr.mm"
include "cin.mm"
include "csup.mm"
include "ffvelrnda.mm"
include "climrecl.mm"
include "mbflimsup.mm"
include "eqeltrrd.mm"

theorem mbflimlem
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vn: setvar n
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let vy: setvar y
  assume mbflim.1: |- Z = ( ZZ>= ` M )
  assume mbflim.2: |- ( ph -> M e. ZZ )
  assume mbflim.4: |- ( ( ph /\ x e. A ) -> ( n e. Z |-> B ) ~~> C )
  assume mbflim.5: |- ( ( ph /\ n e. Z ) -> ( x e. A |-> B ) e. MblFn )
  assume mbflimlem.6: |- ( ( ph /\ ( n e. Z /\ x e. A ) ) -> B e. RR )

  disjoint n x
  disjoint A n
  disjoint A x
  disjoint n ph
  disjoint ph x
  disjoint Z n
  disjoint Z x
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint A j
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n y
  disjoint x y
  disjoint A y
  disjoint C k
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph y
  disjoint Z j
  disjoint Z k
  disjoint Z m
  disjoint Z y
  disjoint B j
  disjoint B k
  disjoint B m
  disjoint B y
  disjoint M j
  disjoint M k
  disjoint M m
  disjoint M y
  assert |- ( ph -> ( x e. A |-> C ) e. MblFn )

  proof
    wph
    vx
    cA
    vn
    cZ
    cB
    cmpt
    #
    clsp
    cfv
    #
    cmpt
    #
    vx
    cA
    cC
    cmpt
    cmbf
    wph
    vx
    cA
    @1
    cC
    wph
    vx
    cv
    cA
    wcel
    #
    wa
    #
    @0
    @1
    cli
    wbr
    @0
    cC
    cli
    wbr
    #
    @1
    cC
    wceq
    @4
    vy
    vj
    vk
    @0
    cM
    cZ
    mbflim.1
    @4
    vn
    cZ
    cB
    cr
    @0
    wph
    vn
    cv
    cZ
    wcel
    @3
    cB
    cr
    wcel
    mbflimlem.6
    anass1rs
    @0
    eqid
    fmptd
    #
    @4
    cM
    cz
    wcel
    #
    @0
    cli
    cdm
    wcel
    #
    vj
    cv
    @0
    cfv
    vk
    cv
    #
    @0
    cfv
    cmin
    co
    cabs
    cfv
    vy
    cv
    clt
    wbr
    vj
    @9
    cuz
    cfv
    wral
    vk
    cZ
    wrex
    vy
    crp
    wral
    wph
    @7
    @3
    mbflim.2
    adantr
    #
    @4
    @5
    @8
    mbflim.4
    @0
    cC
    cli
    climrel
    releldmi
    syl
    vy
    vk
    vj
    @0
    cM
    cZ
    mbflim.1
    climcau
    syl2anc
    caurcvg
    #
    mbflim.4
    @1
    cC
    @0
    climuni
    syl2anc
    mpteq2dva
    wph
    vx
    cA
    cB
    vm
    vn
    @2
    vm
    cr
    @0
    vm
    cv
    cpnf
    cico
    co
    cima
    cxr
    cin
    cxr
    clt
    csup
    cmpt
    #
    cM
    cZ
    mbflim.1
    @2
    eqid
    @12
    eqid
    mbflim.2
    @4
    @1
    vk
    @0
    cM
    cZ
    mbflim.1
    @10
    @11
    @4
    cZ
    cr
    @9
    @0
    @6
    ffvelrnda
    climrecl
    mbflim.5
    mbflimlem.6
    mbflimsup
    eqeltrrd
end
