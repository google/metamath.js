include "c1.mm"
include "cn0.mm"
include "cv.mm"
include "cfv.mm"
include "cabs.mm"
include "cmul.mm"
include "co.mm"
include "cmpt.mm"
include "ccom.mm"
include "cc0.mm"
include "nn0uz.mm"
include "wcel.mm"
include "1nn0.mm"
include "a1i.mm"
include "wa.mm"
include "cr.mm"
include "wceq.mm"
include "id.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "nn0re.mm"
include "cc.mm"
include "psergf.mm"
include "ffvelrnda.mm"
include "abscld.mm"
include "remulcld.mm"
include "eqeltrd.mm"
include "wf.mm"
include "fvco3.mm"
include "sylan.mm"
include "recnd.mm"
include "cbvmptv.mm"
include "radcnvlem1.mm"
include "1red.mm"
include "cuz.mm"
include "cle.mm"
include "cn.mm"
include "elnnuz.mm"
include "nnnn0.mm"
include "sylbir.mm"
include "sylan2.mm"
include "wbr.mm"
include "absge0d.mm"
include "eluzle.mm"
include "lemul1ad.mm"
include "absidm.mm"
include "syl.mm"
include "mulid2d.mm"
include "3eqtr4d.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "3brtr4d.mm"
include "cvgcmpce.mm"

theorem radcnvlem2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vn: setvar n
  let cG: class G
  let cX: class X
  let cY: class Y
  let vi: setvar i
  let vk: setvar k
  let vm: setvar m
  let vs: setvar s
  let vy: setvar y
  let vj: setvar j
  let cH: class H
  let vr: setvar r
  let cN: class N
  let cR: class R
  assume pser.g: |- G = ( x e. CC |-> ( n e. NN0 |-> ( ( A ` n ) x. ( x ^ n ) ) ) )
  assume radcnv.a: |- ( ph -> A : NN0 --> CC )
  assume psergf.x: |- ( ph -> X e. CC )
  assume radcnvlem2.y: |- ( ph -> Y e. CC )
  assume radcnvlem2.a: |- ( ph -> ( abs ` X ) < ( abs ` Y ) )
  assume radcnvlem2.c: |- ( ph -> seq 0 ( + , ( G ` Y ) ) e. dom ~~> )

  disjoint n x
  disjoint A n
  disjoint A x
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i s
  disjoint i x
  disjoint i y
  disjoint A i
  disjoint k m
  disjoint k n
  disjoint k s
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint m n
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n s
  disjoint n y
  disjoint s x
  disjoint s y
  disjoint A s
  disjoint x y
  disjoint A y
  disjoint j m
  disjoint j s
  disjoint H j
  disjoint H m
  disjoint H s
  disjoint i j
  disjoint i ph
  disjoint j k
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint ph s
  disjoint X i
  disjoint X k
  disjoint X m
  disjoint X s
  disjoint X y
  disjoint j r
  disjoint j y
  disjoint G j
  disjoint k r
  disjoint G k
  disjoint m r
  disjoint G m
  disjoint r s
  disjoint r y
  disjoint G r
  disjoint G s
  disjoint G y
  disjoint N n
  disjoint N y
  disjoint R k
  disjoint R y
  disjoint Y i
  disjoint Y j
  disjoint Y k
  disjoint Y m
  assert |- ( ph -> seq 0 ( + , ( abs o. ( G ` X ) ) ) e. dom ~~> )

  proof
    wph
    c1
    vk
    vm
    cn0
    vm
    cv
    #
    @0
    cX
    cG
    cfv
    #
    cfv
    #
    cabs
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    cabs
    @1
    ccom
    #
    cc0
    c1
    cn0
    nn0uz
    c1
    cn0
    wcel
    wph
    1nn0
    a1i
    wph
    vk
    cv
    #
    cn0
    wcel
    #
    wa
    #
    @7
    @5
    cfv
    #
    @7
    @7
    @1
    cfv
    #
    cabs
    cfv
    #
    cmul
    co
    #
    cr
    @8
    @10
    @13
    wceq
    wph
    vm
    @7
    @4
    @13
    cn0
    @5
    @0
    @7
    wceq
    #
    @0
    @7
    @3
    @12
    cmul
    @14
    id
    @14
    @2
    @11
    cabs
    @0
    @7
    @1
    fveq2
    fveq2d
    oveq12d
    #
    @5
    eqid
    @7
    @12
    cmul
    ovex
    fvmpt
    adantl
    #
    @9
    @7
    @12
    @8
    @7
    cr
    wcel
    #
    wph
    @7
    nn0re
    adantl
    #
    @9
    @11
    wph
    cn0
    cc
    @7
    @1
    wph
    vx
    cA
    vn
    cG
    cX
    pser.g
    radcnv.a
    psergf.x
    psergf
    #
    ffvelrnda
    #
    abscld
    #
    remulcld
    #
    eqeltrd
    @9
    @7
    @6
    cfv
    #
    @12
    cc
    wph
    cn0
    cc
    @1
    wf
    @8
    @23
    @12
    wceq
    @19
    cn0
    cc
    @7
    cabs
    @1
    fvco3
    sylan
    #
    @9
    @12
    @21
    recnd
    #
    eqeltrd
    wph
    vx
    cA
    vk
    vn
    cG
    @5
    cX
    cY
    pser.g
    radcnv.a
    psergf.x
    radcnvlem2.y
    radcnvlem2.a
    radcnvlem2.c
    vm
    vk
    cn0
    @4
    @13
    @15
    cbvmptv
    radcnvlem1
    wph
    1red
    wph
    @7
    c1
    cuz
    cfv
    wcel
    #
    wa
    #
    c1
    @12
    cmul
    co
    #
    @13
    @23
    cabs
    cfv
    #
    c1
    @10
    cmul
    co
    #
    cle
    @27
    c1
    @7
    @12
    @27
    1red
    @26
    wph
    @8
    @17
    @26
    @7
    cn
    wcel
    @8
    @7
    elnnuz
    @7
    nnnn0
    sylbir
    #
    @18
    sylan2
    @26
    wph
    @8
    @12
    cr
    wcel
    @31
    @21
    sylan2
    @26
    wph
    @8
    cc0
    @12
    cle
    wbr
    @31
    @9
    @11
    @20
    absge0d
    sylan2
    @26
    c1
    @7
    cle
    wbr
    wph
    c1
    @7
    eluzle
    adantl
    lemul1ad
    @26
    wph
    @8
    @29
    @28
    wceq
    @31
    @9
    @12
    cabs
    cfv
    #
    @12
    @29
    @28
    @9
    @11
    cc
    wcel
    @32
    @12
    wceq
    @20
    @11
    absidm
    syl
    @9
    @23
    @12
    cabs
    @24
    fveq2d
    @9
    @12
    @25
    mulid2d
    3eqtr4d
    sylan2
    @26
    wph
    @8
    @30
    @13
    wceq
    @31
    @9
    @30
    c1
    @13
    cmul
    co
    @13
    @9
    @10
    @13
    c1
    cmul
    @16
    oveq2d
    @9
    @13
    @9
    @13
    @22
    recnd
    mulid2d
    eqtrd
    sylan2
    3brtr4d
    cvgcmpce
end
