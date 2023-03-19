include "cabs.mm"
include "cfv.mm"
include "ccom.mm"
include "cc0.mm"
include "cn0.mm"
include "nn0uz.mm"
include "0zd.mm"
include "cc.mm"
include "wf.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "psergf.mm"
include "fvco3.mm"
include "sylan.mm"
include "ffvelrnda.mm"
include "caddc.mm"
include "cmul.mm"
include "co.mm"
include "cmpt.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "id.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "cbvmptv.mm"
include "radcnvlt1.mm"
include "simprd.mm"
include "abscvgcvg.mm"

theorem radcnvlt2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cR: class R
  let vn: setvar n
  let cG: class G
  let cX: class X
  let vr: setvar r
  let vi: setvar i
  let vk: setvar k
  let vm: setvar m
  let vs: setvar s
  let vy: setvar y
  let vj: setvar j
  let cH: class H
  let cN: class N
  let cY: class Y
  assume pser.g: |- G = ( x e. CC |-> ( n e. NN0 |-> ( ( A ` n ) x. ( x ^ n ) ) ) )
  assume radcnv.a: |- ( ph -> A : NN0 --> CC )
  assume radcnv.r: |- R = sup ( { r e. RR | seq 0 ( + , ( G ` r ) ) e. dom ~~> } , RR* , < )
  assume radcnvlt.x: |- ( ph -> X e. CC )
  assume radcnvlt.a: |- ( ph -> ( abs ` X ) < R )

  disjoint n x
  disjoint A n
  disjoint A x
  disjoint G r
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
  assert |- ( ph -> seq 0 ( + , ( G ` X ) ) e. dom ~~> )

  proof
    wph
    vk
    cabs
    cX
    cG
    cfv
    #
    ccom
    #
    @0
    cc0
    cn0
    nn0uz
    wph
    0zd
    wph
    cn0
    cc
    @0
    wf
    vk
    cv
    #
    cn0
    wcel
    @2
    @1
    cfv
    @2
    @0
    cfv
    #
    cabs
    cfv
    #
    wceq
    wph
    vx
    cA
    vn
    cG
    cX
    pser.g
    radcnv.a
    radcnvlt.x
    psergf
    #
    cn0
    cc
    @2
    cabs
    @0
    fvco3
    sylan
    wph
    cn0
    cc
    @2
    @0
    @5
    ffvelrnda
    wph
    caddc
    vm
    cn0
    vm
    cv
    #
    @6
    @0
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
    cc0
    cseq
    cli
    cdm
    #
    wcel
    caddc
    @1
    cc0
    cseq
    @11
    wcel
    wph
    vx
    cA
    cR
    vk
    vn
    cG
    @10
    cX
    vr
    pser.g
    radcnv.a
    radcnv.r
    radcnvlt.x
    radcnvlt.a
    vm
    vk
    cn0
    @9
    @2
    @4
    cmul
    co
    @6
    @2
    wceq
    #
    @6
    @2
    @8
    @4
    cmul
    @12
    id
    @12
    @7
    @3
    cabs
    @6
    @2
    @0
    fveq2
    fveq2d
    oveq12d
    cbvmptv
    radcnvlt1
    simprd
    abscvgcvg
end
